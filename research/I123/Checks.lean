module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec1
public import RiemannMasullo.AppC_LCTVS.Sec2b
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Tactic
import all RiemannMasullo.AppA_AlgebraicNT.Sec1
import all RiemannMasullo.AppC_LCTVS.Sec1

/-! # Supporting checks for the proposed repair of I123

The accompanying note constructs a valuation fold on the S-local Schwartz space. The
lemmas below check ingredients of that construction. The full S-local strict LF theorem
remains open in the project. Run this file with the project toolchain using
`lake lean research/I123/Checks.lean`.
-/

public section
open RiemannMasullo Function IsDedekindDomain NumberField Topology
open scoped NumberField.AdeleRing DirectSum TensorProduct

namespace MasulloI123

/-- Shell values zero below L and constant above L+M are the finite sum of ball indicators
with coefficients given by first differences. This formulation also allows M = 0. -/
theorem radialBallExpansion (a : ℤ → ℂ) (L : ℤ) (M : ℕ)
    (hlo : ∀ n ≤ L, a n = 0)
    (hhi : ∀ n ≥ L + (M : ℤ), a n = a (L + M)) (n : ℤ) :
    a n = ∑ j ∈ Finset.range M,
      if L + (j : ℤ) < n then a (L + j + 1) - a (L + j) else 0 := by
  have tel (k : ℕ) :
      (∑ j ∈ Finset.range k,
        if L + (j : ℤ) < n then a (L + j + 1) - a (L + j) else 0) =
          a (max L (min n (L + (k : ℤ)))) - a L := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ]
      by_cases h : L + (k : ℤ) < n
      · rw [ite_eq_left h, min_eq_right (by omega), min_eq_right (by omega),
          max_eq_right (by omega), max_eq_right (by omega)]
        rw [← add_assoc L (k : ℤ) 1]
        abel
      · rw [ite_eq_right h, min_eq_left (by omega), min_eq_left (by omega), add_zero]
  rw [tel, hlo L le_rfl, sub_zero]
  by_cases h : n ≤ L
  · rw [max_eq_left (by omega), hlo _ h, hlo _ le_rfl]
  · by_cases h' : n ≤ L + (M : ℤ)
    · rw [min_eq_left h', max_eq_right (by omega)]
    · rw [min_eq_right (by omega), max_eq_right (by omega)]
      exact hhi n (by omega)

open Classical in
theorem valuation_shift {F : Type*} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (v : S) :
    ∃ u : (S : Set (HeightOneSpectrum (𝓞 F))).unit F,
      ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F (u.val : F) =
        if w = v.val then WithZero.exp (-(classNumber F : ℤ)) else 1 := by
  obtain ⟨x, hx⟩ := exists_prime_power_generator F v.val
  let u : (S : Set (HeightOneSpectrum (𝓞 F))).unit F := ⟨x, fun w hw ↦ by
    change w.valuation F (x : F) = 1
    rw [hx, ite_eq_right (show w ≠ v.val from fun e ↦ hw (e.symm ▸ v.property))]⟩
  exact ⟨u, hx⟩

/-- With the finest locally convex topology on the second factor, checking continuity on
the individual archimedean copies indexed by any algebraic basis suffices. -/
theorem continuous_tensor_of_basis
    {A D Z ι : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [PolynormableSpace ℂ A] [T2Space A] [AddCommGroup D] [Module ℂ D]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [PolynormableSpace ℂ Z] [T2Space Z]
    (b : Module.Basis ι ℂ (FinestLocallyConvex D))
    (L : InductiveTensor A (FinestLocallyConvex D) →ₗ[ℂ] Z)
    (h : ∀ i, Continuous fun a : A ↦ L (a ⊗ₜ[ℂ] b i)) : Continuous L := by
  let : T2Space (FinestLocallyConvex D) := finestLocallyConvex_t2 D
  apply (continuous_inductiveTensor_iff L).mpr
  constructor
  · intro a
    exact continuous_of_finestLocallyConvex D (L.comp (TensorProduct.mk ℂ A _ a))
  · intro y
    have hy : y ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; trivial
    let _ := PolynormableSpace.isTopologicalAddGroup ℂ Z
    let L' : A ⊗[ℂ] (FinestLocallyConvex D) →ₗ[ℂ] Z := L
    refine Submodule.span_induction (p := fun y _ ↦ Continuous fun a : A ↦ L' (a ⊗ₜ[ℂ] y))
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, rfl⟩
      exact h i
    · simpa only [TensorProduct.tmul_zero, map_zero] using
        (continuous_const : Continuous fun _ : A ↦ (0 : Z))
    · intro u v _ _ hu hv
      exact (hu.add hv).congr fun a ↦ by
        change L' (a ⊗ₜ[ℂ] u) + L' (a ⊗ₜ[ℂ] v) = L' (a ⊗ₜ[ℂ] (u + v))
        rw [TensorProduct.tmul_add, map_add]
    · intro c u _ hu
      exact (hu.const_smul c).congr fun a ↦ by
        change c • L' (a ⊗ₜ[ℂ] u) = L' (a ⊗ₜ[ℂ] (c • u))
        rw [TensorProduct.tmul_smul, map_smul]

section

variable {E W : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]

/-- Fold redundant valuation coordinates to representatives before taking the quotient. -/
def quotientFold (N : Submodule ℂ E) (j : W →L[ℂ] E) (r : E →L[ℂ] W)
    (hrj : Function.LeftInverse r j) (hfold : ∀ x, N.mkQ (j (r x)) = N.mkQ x) :
    (W ⧸ N.comap j.toLinearMap) ≃L[ℂ] (E ⧸ N) := by
  let M := N.comap j.toLinearMap
  let J := M.liftQL (N.mkQL.comp j) (by
    intro w hw
    exact (Submodule.Quotient.mk_eq_zero N).mpr hw)
  let R := N.liftQL (M.mkQL.comp r) (by
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero M).mpr
    change j (r x) ∈ N
    apply (Submodule.Quotient.mk_eq_zero N).mp
    exact (hfold x).trans ((Submodule.Quotient.mk_eq_zero N).mpr hx))
  refine { J.toLinearMap with
    toFun := J, invFun := R, continuous_toFun := J.continuous, continuous_invFun := R.continuous,
    left_inv := ?_, right_inv := ?_ }
  · intro y
    obtain ⟨w, rfl⟩ := M.mkQ_surjective y
    exact congrArg M.mkQ (hrj w)
  · intro y
    obtain ⟨x, rfl⟩ := N.mkQ_surjective y
    exact hfold x

/-- A character truncation preserving the residual kernel still splits after quotienting. -/
theorem quotientStage_closedEmbedding (N : Submodule ℂ E) [T2Space (E ⧸ N)]
    (j : W →L[ℂ] E) (r : E →L[ℂ] W) (hrj : Function.LeftInverse r j)
    (hN : ∀ x ∈ N, j (r x) ∈ N) :
    Topology.IsClosedEmbedding
      ((N.comap j.toLinearMap).liftQL (N.mkQL.comp j) (by
        intro w hw
        exact (Submodule.Quotient.mk_eq_zero N).mpr hw)) := by
  let M := N.comap j.toLinearMap
  let R := N.liftQL (M.mkQL.comp r) (by
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero M).mpr (hN x hx))
  apply Function.LeftInverse.isClosedEmbedding (f := R) _ R.continuous (ContinuousLinearMap.continuous _)
  intro y
  obtain ⟨w, rfl⟩ := M.mkQ_surjective y
  exact congrArg M.mkQ (hrj w)

end

/-- Quotienting each character summand gives the original locally convex quotient topology. -/
theorem characterQuotients (W : ℕ → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
    (N : ∀ i, Submodule ℂ (W i)) :
    let := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ W)
    let := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ (fun i ↦ W i ⧸ N i))
    IsQuotientMap (DirectSum.lmap (fun i ↦ (N i).mkQ)) :=
  isQuotientMap_directSum_lmap (fun i ↦ (N i).mkQ) (fun i ↦ (N i).isQuotientMap_mkQ)

section
variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}
local notation "B" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "U" => (SAdeleRing F S)ˣ
local notation "J" => SIdeleQuotient F S
local notation "θ" => sLocalAdelicTheta F S

theorem theta_translate (g x : U) (f : B) :
    θ (schwartzBruhatUnitTranslate g f) x = θ f (g⁻¹ * x) := by
  let d := (Units.map ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom).comp
    (Units.map (integralAdeleDiagonal F S).toMonoidHom)
  refine (sLocalAdelicTheta_apply F S (schwartzBruhatUnitTranslate g f) x).trans
    (Eq.trans ?_ (sLocalAdelicTheta_apply F S f (g⁻¹ * x)).symm)
  exact tsum_congr fun t ↦ congrArg (fun y ↦ f (Multiplicative.ofAdd y))
    (mul_left_comm g.inv (d t).val x.val)

theorem translate_mem_thetaKer (g : U) {f : B} (hf : f ∈ (θ).ker) :
    schwartzBruhatUnitTranslate g f ∈ (θ).ker := by
  apply ContinuousMap.ext
  intro x
  exact (theta_translate g x f).trans (congrArg (fun h ↦ h (g⁻¹ * x)) (LinearMap.mem_ker.mp hf))

theorem principal_translate_thetaClass (g : U) (hg : (QuotientGroup.mk g : J) = 1) (f : B) :
    (θ).ker.mkQ (schwartzBruhatUnitTranslate g f) = (θ).ker.mkQ f := by
  simp only [Submodule.mkQ_apply, Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]
  apply ContinuousMap.ext
  intro x
  refine (theta_translate g x f).trans ((sLocalAdelicTheta_factorsThrough F S f) ?_)
  change (QuotientGroup.mk' _ (g⁻¹ * x) : J) = QuotientGroup.mk' _ x
  rw [map_mul, map_inv]
  change (QuotientGroup.mk g : J)⁻¹ * _ = _
  rw [hg, inv_one, one_mul]
end

#print axioms radialBallExpansion
#print axioms valuation_shift
#print axioms continuous_tensor_of_basis
#print axioms quotientFold
#print axioms quotientStage_closedEmbedding
#print axioms characterQuotients
#print axioms theta_translate
#print axioms translate_mem_thetaKer
#print axioms principal_translate_thetaClass

end MasulloI123
