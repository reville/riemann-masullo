module
public import RiemannMasullo.Ch02_AdelicTheta.Sec1
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.LocallyConstant.Basic
import all RiemannMasullo.Ch02_AdelicTheta.Sec1

public noncomputable section
open RiemannMasullo Function IsDedekindDomain NumberField Set Topology

namespace MasulloI123Exact

/-- Subtracting the constant term on the integer ball leaves finite multiplicative
coset support, also for vector-valued coefficients. -/
theorem localVectorCosetExpansion {F V : Type*} [Field F] [NumberField F] [AddCommGroup V]
    (v : HeightOneSpectrum (𝓞 F)) (H : OpenSubgroup (v.adicCompletion F)ˣ)
    (hH : H.toSubgroup ≤ (v.adicCompletionIntegers F).units) (g : v.adicCompletion F → V)
    (hg : IsLocallyConstant g) (hgc : HasCompactSupport g)
    (hfix : ∀ h ∈ H, ∀ x, g (h.val * x) = g x) :
    ∃ b : ((v.adicCompletion F)ˣ ⧸ H.toSubgroup) →₀ V,
      ∀ u : (v.adicCompletion F)ˣ, g u.val =
        (v.adicCompletionIntegers F : Set _).indicator (fun _ ↦ g 0) u.val + b (QuotientGroup.mk u) := by
  classical
  let K := v.adicCompletion F
  let Q := Kˣ ⧸ H.toSubgroup
  let O := v.adicCompletionIntegers F
  have hOc : IsCompact (O : Set K) := isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)
  let s := (LocallyConstant.const K (g 0)).indicator (show IsClopen (O : Set K) from
    ⟨hOc.isClosed, Valued.isOpen_valuationSubring _⟩)
  have hs : HasCompactSupport (s : K → V) := by
    apply hOc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hOc.isClosed
    intro x hx
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  let d (x : K) := g x - s x
  have dl : IsLocallyConstant d := hg.comp₂ s.isLocallyConstant (· - ·)
  have dc : HasCompactSupport d := hgc.sub hs
  have d0 : d 0 = 0 := by
    change g 0 - (O : Set K).indicator (fun _ ↦ g 0) 0 = 0
    rw [Set.indicator_of_mem O.zero_mem, sub_self]
  have hz : (0 : K) ∉ tsupport d := by
    have hh : IsClosed (support d) := (dl.isClopen_fiber 0).isOpen.isClosed_compl
    exact fun h ↦ (hh.closure_eq ▸ h : 0 ∈ support d) d0
  have inv (h : Kˣ) (hh : h ∈ H) (x : K) : d (h.val * x) = d x := by
    have hg' : g (h.val * x) = g x := hfix h hh x
    have equiv : h.val * x ∈ O ↔ x ∈ O := by
      constructor
      · intro hx
        have he := O.toSubring.mul_mem (show h.inv ∈ O from (hH hh).2) hx
        change h.inv * (h.val * x) ∈ O at he
        rwa [← mul_assoc, h.inv_val, one_mul] at he
      · exact O.toSubring.mul_mem (show h.val ∈ O from (hH hh).1)
    have eqs : s (h.val * x) = s x := by
      change (O : Set K).indicator (fun _ ↦ g 0) (h.val * x) = (O : Set K).indicator (fun _ ↦ g 0) x
      by_cases hx : x ∈ O
      · rw [Set.indicator_of_mem (equiv.mpr hx), Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem (fun h ↦ hx (equiv.mp h)), Set.indicator_of_notMem hx]
    exact congrArg₂ (· - ·) hg' eqs
  let Z := tsupport d
  let lift (x : Z) : Kˣ := Units.mk0 x.val (fun he ↦ hz (he ▸ x.property))
  let key (x : Z) : Q := QuotientGroup.mk (lift x)
  have hl : Continuous lift := IsOpenUnits.isOpenEmbedding_unitsVal.isInducing.continuous_iff.mpr continuous_subtype_val
  have hfin : (range key).Finite :=
    let : CompactSpace Z := isCompact_iff_compactSpace.mp dc
    (isCompact_range (QuotientGroup.continuous_mk.comp hl)).finite_of_discrete
  let c (q : Q) := d (q.out : Kˣ).val
  have hc (u : Kˣ) : c (QuotientGroup.mk u) = d u.val := by
    let z : Kˣ := (QuotientGroup.mk u : Q).out
    have he : (QuotientGroup.mk z : Q) = QuotientGroup.mk u := Quotient.out_eq' _
    have := inv (z / u) (QuotientGroup.eq_iff_div_mem.mp he) u.val
    simpa only [Units.val_div_eq_div_val, div_mul_cancel₀ _ u.ne_zero] using this
  have hsupp : (support c).Finite := hfin.subset (by
    intro q hq
    have hx : (q.out : Kˣ).val ∈ Z := subset_tsupport d hq
    refine ⟨⟨_,hx⟩, ?_⟩
    have eu : lift ⟨(q.out : Kˣ).val,hx⟩ = q.out := Units.ext rfl
    exact (congrArg (fun u : Kˣ ↦ (QuotientGroup.mk u : Q)) eu).trans (Quotient.out_eq' q))
  refine ⟨Finsupp.ofSupportFinite c hsupp, fun u ↦ ?_⟩
  change g u.val = s u.val + c (QuotientGroup.mk u)
  rw [hc]
  change g u.val = s u.val + (g u.val - s u.val)
  abel

/-- An invariant test at one finite place consists of its value at zero on the integer
ball and a finitely supported function on multiplicative cosets. -/
theorem localCosetExpansion {F : Type*} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (H : OpenSubgroup (v.adicCompletion F)ˣ)
    (hH : H.toSubgroup ≤ (v.adicCompletionIntegers F).units)
    (f : SchwartzBruhat (Multiplicative (v.adicCompletion F)))
    (hf : ∀ h ∈ H, schwartzBruhatUnitTranslate h f = f) :
    ∃ b : ((v.adicCompletion F)ˣ ⧸ H.toSubgroup) →₀ ℂ,
      ∀ u : (v.adicCompletion F)ˣ, f (Multiplicative.ofAdd u.val) =
        (v.adicCompletionIntegers F : Set _).indicator (fun _ ↦ f (Multiplicative.ofAdd 0)) u.val +
        b (QuotientGroup.mk u) := by
  obtain ⟨hg,hgc⟩ := (mem_finitePlaceSchwartz_iff F v _).mp ⟨f, fun _ ↦ rfl⟩
  exact localVectorCosetExpansion v H hH (fun x ↦ f (Multiplicative.ofAdd x)) hg hgc
    (fun h hh x ↦ congrArg (fun z : SchwartzBruhat _ ↦ z (Multiplicative.ofAdd x)) (hf h⁻¹ (H.inv_mem hh)))

/-- The multiplicative-coset expansion can be iterated in a product. The same
finite list of cosets works for every value of the other coordinates, and all
coefficient functions are again locally constant and compactly supported. -/
theorem productCosetExpansion {F A V : Type*} [Field F] [NumberField F]
    [TopologicalSpace A] [T2Space A] [AddCommGroup V]
    (v : HeightOneSpectrum (𝓞 F)) (H : OpenSubgroup (v.adicCompletion F)ˣ)
    (hH : H.toSubgroup ≤ (v.adicCompletionIntegers F).units) (g : A × v.adicCompletion F → V)
    (hg : IsLocallyConstant g) (hc : HasCompactSupport g)
    (hfix : ∀ h ∈ H, ∀ x y, g (x, h.val * y) = g (x,y)) :
    let O : Set (v.adicCompletion F) := v.adicCompletionIntegers F
    ∃ b : ((v.adicCompletion F)ˣ ⧸ H.toSubgroup) →₀ (A → V),
      (IsLocallyConstant (fun x ↦ g (x,0)) ∧ HasCompactSupport (fun x ↦ g (x,0))) ∧
      (∀ q, IsLocallyConstant (b q) ∧ HasCompactSupport (b q)) ∧
      (∀ (r : A → A), (∀ x y, g (r x,y) = g (x,y)) → ∀ q x, b q (r x) = b q x) ∧
      ∀ (u : (v.adicCompletion F)ˣ) (x : A),
        g (x, u.val) = O.indicator (fun _ ↦ g (x,0)) u.val + b (QuotientGroup.mk u) x := by
  classical
  intro O
  let K := v.adicCompletion F
  let W (y : K) (x : A) := g (x,y)
  let P := Prod.fst '' tsupport g
  have hP : IsCompact P := hc.image continuous_fst
  have hzero (x : A) (hx : x ∉ P) (y : K) : W y x = 0 := by
    by_contra h
    exact hx ⟨(x,y), subset_tsupport g h, rfl⟩
  have hslice (y : K) : IsLocallyConstant (W y) ∧ HasCompactSupport (W y) := by
    refine ⟨hg.comp_continuous (continuous_id.prodMk continuous_const), ?_⟩
    exact hP.of_isClosed_subset (isClosed_tsupport _) (closure_minimal
      (fun x hx ↦ by_contra (fun h ↦ hx (hzero x h y))) hP.isClosed)
  have hW : IsLocallyConstant W := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro y
    let B := {p : K × A | g (p.2,p.1) = g (p.2,y)}
    have hB : IsOpen B := ((hg.comp_continuous continuous_swap).prodMk
      (hg.comp_continuous (continuous_snd.prodMk continuous_const))) {p | p.1 = p.2}
    obtain ⟨U,D,hU,_,hy,hPD,hUD⟩ := generalized_tube_lemma (isCompact_singleton (x := y)) hP hB
      (show {y} ×ˢ P ⊆ B by rintro ⟨_,x⟩ ⟨rfl,_⟩; rfl)
    refine ⟨U,hU,hy rfl,fun z hz ↦ funext fun x ↦ ?_⟩
    by_cases hx : x ∈ P
    · exact hUD (mk_mem_prod hz (hPD hx))
    · exact (hzero x hx z).trans (hzero x hx y).symm
  have hWc : HasCompactSupport W := by
    have c := hc.image continuous_snd
    apply c.of_isClosed_subset (isClosed_tsupport _) (closure_minimal _ c.isClosed)
    intro y hy
    by_contra h
    exact hy (funext fun x ↦ by_contra (fun hn ↦ h ⟨(x,y),subset_tsupport g hn,rfl⟩))
  obtain ⟨b,hb⟩ := localVectorCosetExpansion v H hH W hW hWc
    (fun h hh y ↦ funext fun x ↦ hfix h hh x y)
  refine ⟨b,hslice 0,fun q ↦ ?_,fun r hr q x ↦ ?_,fun u x ↦ ?_⟩
  · let u : Kˣ := q.out
    have h := hb u
    rw [show (QuotientGroup.mk u : Kˣ ⧸ H.toSubgroup) = q from Quotient.out_eq' _] at h
    by_cases hx : u.val ∈ O
    · rw [Set.indicator_of_mem hx] at h
      have eq : b q = W u.val - W 0 := by rw [h]; abel
      rw [eq]
      exact ⟨(hslice _).1.comp₂ (hslice _).1 (· - ·), (hslice _).2.sub (hslice _).2⟩
    · rw [Set.indicator_of_notMem hx, zero_add] at h
      exact h ▸ hslice u.val
  · let u : Kˣ := q.out
    have he : W u.val = O.indicator (fun _ ↦ W 0) u.val + b (QuotientGroup.mk u) := hb u
    rw [show (QuotientGroup.mk u : Kˣ ⧸ H.toSubgroup) = q from Quotient.out_eq' _] at he
    have eq : b q = W u.val - O.indicator (fun _ ↦ W 0) u.val := by rw [he]; abel
    rw [eq]
    by_cases hu : u.val ∈ O
    · simp only [Set.indicator_of_mem hu, Pi.sub_apply]
      exact congrArg₂ (· - ·) (hr x u.val) (hr x 0)
    · simp only [Set.indicator_of_notMem hu, sub_zero]
      exact hr x u.val
  · have he : W u.val = O.indicator (fun _ ↦ W 0) u.val + b (QuotientGroup.mk u) := hb u
    have hx := congrFun he x
    by_cases hu : u.val ∈ O
    · simpa only [Set.indicator_of_mem hu, Pi.add_apply] using hx
    · simpa only [Set.indicator_of_notMem hu, zero_add] using hx

/-- The integer-ball indicator and the unit-subgroup indicator give two explicit
seed tests at one place. Translating the latter produces every coset in the
expansion, including the correct value at zero. -/
theorem twoLocalSeeds {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (H : OpenSubgroup (v.adicCompletion F)ˣ) (hH : H.toSubgroup ≤ (v.adicCompletionIntegers F).units) :
    ∃ b₀ b₁ : SchwartzBruhat (Multiplicative (v.adicCompletion F)),
      ∀ f : SchwartzBruhat (Multiplicative (v.adicCompletion F)),
        (∀ h ∈ H, schwartzBruhatUnitTranslate h f = f) →
        ∃ c : ((v.adicCompletion F)ˣ ⧸ H.toSubgroup) →₀ ℂ, ∀ x : v.adicCompletion F,
          f (Multiplicative.ofAdd x) = f (Multiplicative.ofAdd 0) * b₀ (Multiplicative.ofAdd x) +
            ∑ q ∈ c.support, c q * schwartzBruhatUnitTranslate q.out b₁ (Multiplicative.ofAdd x) := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let Q := Kˣ ⧸ H.toSubgroup
  have hO : IsCompact (O : Set K) := isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)
  obtain ⟨b₀,h₀⟩ := finitePlaceSchwartz_compactOpen_indicator F v (O : Set K) hO (Valued.isOpen_valuationSubring _)
  let U : Set K := Units.val '' (H : Set Kˣ)
  have hC : IsCompact (H : Set Kˣ) :=
    (Submonoid.units_isCompact hO).of_isClosed_subset (H.toSubgroup.isClosed_of_isOpen H.isOpen) hH
  obtain ⟨b₁,h₁⟩ := finitePlaceSchwartz_compactOpen_indicator F v U (hC.image Units.continuous_val)
    (IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _ H.isOpen)
  refine ⟨b₀,b₁,fun f hf ↦ ?_⟩
  obtain ⟨c,hc⟩ := localCosetExpansion v H hH f hf
  refine ⟨c, fun x ↦ ?_⟩
  have hball : f (Multiplicative.ofAdd 0) * b₀ (Multiplicative.ofAdd x) =
      (O : Set K).indicator (fun _ ↦ f (Multiplicative.ofAdd 0)) x := by
    rw [h₀]
    by_cases h : x ∈ O <;> simp [Set.indicator, h]
  rw [hball]
  by_cases hx : x = 0
  · subst x
    have hz : (0 : K) ∉ U := by rintro ⟨u,_,hu⟩; exact u.ne_zero hu
    have hzero (q : Q) : schwartzBruhatUnitTranslate q.out b₁ (Multiplicative.ofAdd 0) = 0 := by
      rw [schwartzBruhatUnitTranslate_apply, mul_zero, h₁, Set.indicator_of_notMem hz]
    rw [Set.indicator_of_mem O.zero_mem, Finset.sum_eq_zero (fun q _ ↦ (congrArg (c q * ·) (hzero q)).trans (mul_zero _)), add_zero]
  · let u := Units.mk0 x hx
    have hv (q : Q) : schwartzBruhatUnitTranslate q.out b₁ (Multiplicative.ofAdd x) =
        if q = QuotientGroup.mk u then (1 : ℂ) else 0 := by
      rw [schwartzBruhatUnitTranslate_apply, h₁]
      have he : q.out.inv * x ∈ U ↔ q = QuotientGroup.mk u := by
        have h1 : q.out.inv * x ∈ U ↔ u / q.out ∈ H := by
          have hv : (u / q.out).val = q.out.inv * x := mul_comm _ _
          rw [← hv]
          exact ⟨fun ⟨a,ha,eq⟩ ↦ Units.val_injective eq ▸ ha, fun h ↦ ⟨_,h,rfl⟩⟩
        rw [h1]
        change u / q.out ∈ H.toSubgroup ↔ _
        rw [← QuotientGroup.eq_iff_div_mem, show (QuotientGroup.mk q.out : Q) = q from Quotient.out_eq' _]
        exact eq_comm
      change (if q.out.inv * x ∈ U then (1 : ℂ) else 0) = _
      exact if_congr he rfl rfl
    refine (hc u).trans (congrArg ((O : Set K).indicator (fun _ ↦ f (Multiplicative.ofAdd 0)) x + ·) ?_)
    simp only [hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finsupp.mem_support_iff]
    split_ifs with h <;> simp_all

#print axioms twoLocalSeeds

#print axioms productCosetExpansion
#print axioms localVectorCosetExpansion
#print axioms localCosetExpansion
end MasulloI123Exact
