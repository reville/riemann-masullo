module
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import Mathlib.Topology.Algebra.Group.Units
public import RiemannMasullo.ForMathlib.Topology.Algebra.OpenSubgroup
import all RiemannMasullo.Ch02_AdelicTheta.Sec1
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec2
import all RiemannMasullo.Ch02_AdelicTheta.Sec2b
import all RiemannMasullo.Ch02_AdelicTheta.Sec3
import all RiemannMasullo.AppC_LCTVS.Sec1

public noncomputable section
open TopologicalSpace RiemannMasullo Function IsDedekindDomain NumberField Set Topology Filter
open scoped NumberField.AdeleRing TensorProduct

namespace MasulloI123Exact

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

abbrev IntegralUnits (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :=
  (v : S) → ↥((v.val.adicCompletionIntegers F).units)

def finiteLocalUnit (k : IntegralUnits F S) : (FinitePlaceProduct F S)ˣ :=
  (ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)).symm (fun v ↦ (k v).val)

def finiteUnitIdele : IntegralUnits F S →* (SAdeleRing F S)ˣ where
  toFun k := (MulEquiv.prodUnits ..).symm (1, finiteLocalUnit k)
  map_one' := Units.ext (Prod.ext rfl (funext fun _ ↦ rfl))
  map_mul' _ _ := Units.ext (Prod.ext (by change (1 : InfiniteAdeleRing F) = 1 * 1; exact (one_mul _).symm) (funext fun _ ↦ rfl))

theorem continuous_finiteUnitIdele :
    Continuous (finiteUnitIdele (F := F) (S := S)) := by
  let p := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) (FinitePlaceProduct F S)
  let f := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
  exact p.symm.continuous.comp (continuous_const.prodMk
    (f.symm.continuous.comp (continuous_pi fun v ↦ continuous_subtype_val.comp (continuous_apply v))))

theorem finiteLocalOrbit (g : SchwartzBruhat (Multiplicative (FinitePlaceProduct F S))) :
    (range fun k : IntegralUnits F S ↦ schwartzBruhatUnitTranslate (finiteLocalUnit k) g).Finite := by
  let C := univ.pi (fun w : S ↦ (w.val.adicCompletionIntegers F : Set (w.val.adicCompletion F)))
  have hC : IsCompact C := isCompact_univ_pi
    (fun w : S ↦ isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers w.val))
  let : TotallyDisconnectedSpace (Multiplicative (FinitePlaceProduct F S)) :=
    inferInstanceAs (TotallyDisconnectedSpace ((w : S) → w.val.adicCompletion F))
  have hg := schwartzBruhat_locallyConstant_compactSupport (finitePlaceProduct_compact_subset_subgroup F S) g
  apply (finite_unit_dilates C hC g hg.1 hg.2).subset
  rintro _ ⟨k, rfl⟩
  exact ⟨⟨finiteLocalUnit k, fun w _ ↦ (k w).property.1, fun w _ ↦ (k w).property.2⟩, rfl⟩

theorem finiteTestOrbit (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    (range fun k : IntegralUnits F S ↦ schwartzBruhatUnitTranslate (finiteUnitIdele k) f).Finite := by
  let A := Multiplicative (InfiniteAdeleRing F)
  let : T2Space A := inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology A := inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  obtain ⟨e, he⟩ := kernel_with_finitePlaceProduct F (G := A) S (archFiniteProductEquiv F S)
  obtain ⟨z, rfl⟩ := e.surjective f
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    apply ((finiteLocalOrbit b).image (fun c ↦ e (a ⊗ₜ[ℂ] c))).subset
    rintro _ ⟨k, rfl⟩
    refine ⟨_, ⟨k, rfl⟩, ?_⟩
    apply Subtype.ext
    funext x
    let y := Multiplicative.ofAdd ((finiteUnitIdele k).inv * x.toAdd)
    refine (he a (schwartzBruhatUnitTranslate (finiteLocalUnit k) b) x).trans (Eq.trans ?_ (he a b y).symm)
    change a (Multiplicative.ofAdd x.toAdd.1) * _ =
      a (Multiplicative.ofAdd ((1 : InfiniteAdeleRing F) * x.toAdd.1)) * _
    rw [one_mul]
    rfl
  | add x y hx hy =>
    apply (hx.image2 (· + ·) hy).subset
    rintro _ ⟨k, rfl⟩
    refine ⟨_, ⟨k, rfl⟩, _, ⟨k, rfl⟩, ?_⟩
    exact congrArg (schwartzBruhatUnitTranslate (finiteUnitIdele k)) (e.map_add x y).symm


/-- Translation by a finite integral unit, acting on the actual theta quotient. -/
def localAction : IntegralUnits F S →* (SLocalAdelicThetaSpace F S →L[ℂ] SLocalAdelicThetaSpace F S) :=
  (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose.comp
    ((QuotientGroup.mk' _).comp finiteUnitIdele)

/-- Every theta class has finite orbit under the finite-place integral units. -/
theorem finiteThetaOrbit (x : SLocalAdelicThetaSpace F S) :
    (range fun k : IntegralUnits F S ↦ localAction k x).Finite := by
  let N := (sLocalAdelicTheta F S).ker
  obtain ⟨f, rfl⟩ := N.mkQ_surjective x
  apply ((finiteTestOrbit f).image N.mkQ).subset
  rintro _ ⟨k, rfl⟩
  refine ⟨_, ⟨k, rfl⟩, ?_⟩
  exact ((existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2
    (finiteUnitIdele k) f).symm

/-- Each open subgroup of the integral product contains independent open local
levels. They are open in the full multiplicative local fields as well. -/
theorem coordinateLevels (H : OpenSubgroup (IntegralUnits F S)) :
    ∃ U : (v : S) → OpenSubgroup (v.val.adicCompletion F)ˣ,
      (∀ v, (U v).toSubgroup ≤ (v.val.adicCompletionIntegers F).units) ∧
      (∀ k : IntegralUnits F S, (∀ v, (k v).val ∈ U v) → k ∈ H) := by
  classical
  let O (v : S) := (v.val.adicCompletionIntegers F).units
  let i (v : S) := MonoidHom.mulSingle (fun w : S ↦ ↥(O w)) v
  let V (v : S) := OpenSubgroup.comap (i v) (continuous_mulSingle (A := fun w : S ↦ ↥(O w)) v) H
  let U (v : S) := (V v).toSubgroup.map (O v).subtype
  have hopen (v : S) : IsOpen (U v : Set (v.val.adicCompletion F)ˣ) := by
    have ho : IsOpen (O v : Set (v.val.adicCompletion F)ˣ) :=
      Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
    exact ho.isOpenEmbedding_subtypeVal.isOpenMap _ (V v).isOpen
  refine ⟨fun v ↦ ⟨U v,hopen v⟩, fun v _ ⟨z,_,hz⟩ ↦ hz ▸ z.property, fun k hk ↦ ?_⟩
  have hmem (v : S) : i v (k v) ∈ H := by
    obtain ⟨b,hb,he⟩ := hk v
    have h : b = k v := Subtype.ext he
    exact h ▸ hb
  have he : ∏ v, i v (k v) = k := by
    ext v : 1
    change (∏ w, Pi.mulSingle w (k w)) v = k v
    rw [Finset.prod_apply, Finset.prod_eq_single v]
    · exact Pi.mulSingle_eq_same _ _
    · intro w _ hw
      exact Pi.mulSingle_eq_of_ne (Ne.symm hw) _
    · simp
  exact he ▸ H.prod_mem (fun v _ ↦ hmem v)

#print axioms coordinateLevels

/-- The vectors fixed by every element of an open subgroup of the finite units. -/
def fixedStage (H : OpenSubgroup (IntegralUnits F S)) : Submodule ℂ (SLocalAdelicThetaSpace F S) where
  carrier := {x | ∀ k ∈ H, localAction k x = x}
  zero_mem' := fun _ _ ↦ map_zero _
  add_mem' hx hy k hk := by rw [map_add, hx k hk, hy k hk]
  smul_mem' c _ hx k hk := by rw [map_smul, hx k hk]

theorem fixedStage_closed (H : OpenSubgroup (IntegralUnits F S)) :
    IsClosed (fixedStage H : Set (SLocalAdelicThetaSpace F S)) := by
  let : T2Space (SLocalAdelicThetaSpace F S) :=
    sLocalAdelicThetaSpace_t2_of_isClosed sLocalAdelicTheta_ker_isClosed
  change IsClosed {x | ∀ k ∈ H, localAction k x = x}
  simp only [ofPred_forall]
  exact isClosed_biInter fun k (_ : k ∈ H) ↦ isClosed_eq (localAction k).continuous continuous_id

/-- A theta class fixed by a compact open subgroup has a test representative
fixed by that same subgroup, by averaging the finite orbit of any representative. -/
theorem fixedStage_lifts (H : OpenSubgroup (IntegralUnits F S))
    {x : SLocalAdelicThetaSpace F S} (hx : x ∈ fixedStage H) :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      (sLocalAdelicTheta F S).ker.mkQ f = x ∧
      ∀ k ∈ H, schwartzBruhatUnitTranslate (finiteUnitIdele k) f = f := by
  classical
  let N := (sLocalAdelicTheta F S).ker
  obtain ⟨f, rfl⟩ := N.mkQ_surjective x
  let r := (unitTranslateEnd (R := SAdeleRing F S)).comp
    (finiteUnitIdele.comp H.toSubgroup.subtype)
  have fin : (range fun h : H ↦ r h f).Finite := (finiteTestOrbit f).subset (by
    rintro _ ⟨h,rfl⟩
    exact ⟨h.val,rfl⟩)
  let O := fin.toFinset
  have hO : O.Nonempty := ⟨r 1 f, fin.mem_toFinset.mpr ⟨1,rfl⟩⟩
  have hq : ∀ y ∈ O, N.mkQ y = N.mkQ f := by
    intro y hy
    obtain ⟨k,rfl⟩ := fin.mem_toFinset.mp hy
    exact ((existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2
      (finiteUnitIdele k.val) f).symm.trans (hx k.val k.property)
  refine ⟨(O.card : ℂ)⁻¹ • ∑ y ∈ O, y, ?_, fun k hk ↦ ?_⟩
  · change N.mkQ _ = N.mkQ f
    rw [map_smul, map_sum, Finset.sum_congr rfl hq, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hO.card_pos.ne'), one_smul]
  · let k' : H := ⟨k,hk⟩
    exact (map_smul (r k') _ _).trans
      (congrArg ((O.card : ℂ)⁻¹ • ·) (sum_orbit_invariant r f fin k'))

/-- A single decreasing basis of compact open unit subgroups gives a rising, closed
cover of the theta quotient. No strictness or completeness of this quotient is used. -/
theorem theta_fixedStage_cover :
    ∃ H : ℕ → OpenSubgroup (IntegralUnits F S), Antitone H ∧
      (∀ n, IsCompact (H n : Set (IntegralUnits F S))) ∧
      (∀ x : SLocalAdelicThetaSpace F S, ∃ n, x ∈ fixedStage (H n)) := by
  let K := IntegralUnits F S
  let Q := SLocalAdelicThetaSpace F S
  let : T2Space Q := sLocalAdelicThetaSpace_t2_of_isClosed sLocalAdelicTheta_ker_isClosed
  let (v : S) : CompactSpace ↥((v.val.adicCompletionIntegers F).units) :=
    isCompact_iff_compactSpace.mp (Submonoid.units_isCompact
      (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v.val)))
  let (v : S) : TotallyDisconnectedSpace ↥((v.val.adicCompletionIntegers F).units) := by
    let : TotallyDisconnectedSpace (v.val.adicCompletion F)ˣ :=
      ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
        Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
    infer_instance
  let (v : S) : FirstCountableTopology ↥((v.val.adicCompletionIntegers F).units) := by
    let : FirstCountableTopology (v.val.adicCompletion F)ˣ :=
      (Units.isInducing_embedProduct (M := v.val.adicCompletion F)).firstCountableTopology
    exact IsInducing.subtypeVal.firstCountableTopology
  let : CompactSpace K := Pi.compactSpace
  let : TotallyDisconnectedSpace K := inferInstanceAs (TotallyDisconnectedSpace (∀ v : S, _))
  let : FirstCountableTopology K := inferInstanceAs (FirstCountableTopology (∀ v : S, _))
  have hb : (𝓝 (1 : K)).HasBasis (fun H : OpenSubgroup K ↦ IsCompact (H : Set K)) (fun H ↦ (H : Set K)) := by
    refine ⟨fun W ↦ ⟨exists_compact_openSubgroup_sub_mem_nhds, ?_⟩⟩
    rintro ⟨H, _, h⟩
    exact mem_of_superset H.mem_nhds_one h
  obtain ⟨H, hcomp, hH⟩ := hb.exists_antitone_subbasis
  refine ⟨H, hH.antitone, hcomp, fun x ↦ ?_⟩
  let t : K → Q := fun k ↦ localAction k x
  have ht : Continuous t :=
    (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.1.comp
      ((QuotientGroup.continuous_mk.comp continuous_finiteUnitIdele).prodMk continuous_const)
  have h1 : t 1 = x := by simp [t]
  let bad := range t \ {x}
  have ho : IsOpen (t ⁻¹' badᶜ) := ((finiteThetaOrbit x).sdiff.isClosed.isOpen_compl).preimage ht
  obtain ⟨n, hn⟩ := hH.mem_iff.mp (ho.mem_nhds (by simp [bad, h1]))
  refine ⟨n, fun k hk ↦ ?_⟩
  by_contra h
  exact hn hk ⟨⟨k, rfl⟩, h⟩

section ClosedImages

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]

/-- A continuous injection between Fréchet spaces with closed image is an embedding,
by applying the open mapping theorem onto its image. -/
private theorem frechetEmbedding {A B : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    (hA : IsFrechetTVS A) (hB : IsFrechetTVS B) (f : A →L[ℂ] B)
    (hi : Injective f) (hc : IsClosed (range f)) : IsEmbedding f := by
  let : IsTopologicalAddGroup A := hA.1
  let : IsTopologicalAddGroup B := hB.1
  let : PolynormableSpace ℂ A := hA.2.1
  let : MetrizableSpace A := hA.2.2.1
  let R := f.toLinearMap.range
  let g := f.codRestrict R (fun x ↦ ⟨x, rfl⟩)
  have hs : Surjective g := fun z ↦ z.property.elim fun x hx ↦ ⟨x, Subtype.ext hx⟩
  have hR := frechet_of_closed_embedding R.subtypeL hc.isClosedEmbedding_subtypeVal hB
  have ho := isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hR) (X := fun _ ↦ A)
    (fun _ ↦ hA) (fun _ ↦ ContinuousLinearMap.id ℂ A) (fun _ ↦ Subset.rfl)
    (fun x ↦ ⟨0, x, rfl⟩) g hs
  let e := Equiv.ofBijective g ⟨fun _ _ he ↦ hi (congrArg Subtype.val he), hs⟩
  exact IsEmbedding.subtypeVal.comp (e.toHomeomorphOfContinuousOpen g.continuous ho).isEmbedding

/-- Closed ascending images of Fréchet injections exhausting an LF-space make it
strict, even when the maps initially come without a proof of embedding. -/
theorem strictLF_of_closed_frechet_images {X : ℕ → Type*}
    [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
    (lf : IsLFSpace E) (hX : ∀ n, IsFrechetTVS (X n)) (u : ∀ n, X n →L[ℂ] E)
    (hi : ∀ n, Injective (u n)) (hr : ∀ n, range (u n) ⊆ range (u (n+1)))
    (hc : ∀ n, IsClosed (range (u n))) (cover : ∀ x, ∃ n, x ∈ range (u n)) :
    IsStrictLFSpace E := by
  let R n := (u n).toLinearMap.range
  have step (n : ℕ) : ∃ v : X n →L[ℂ] X (n+1), (u (n+1)).comp v = u n := by
    let b := (u (n+1)).codRestrict (R (n+1)) (fun x ↦ ⟨x,rfl⟩)
    let a := (u n).codRestrict (R (n+1)) (fun x ↦ hr n ⟨x,rfl⟩)
    have sur : Surjective b := fun z ↦ z.property.elim fun x hx ↦ ⟨x, Subtype.ext hx⟩
    obtain ⟨_, v, hv⟩ := frechet_factorization (X := fun _ ↦ X (n+1)) (fun _ ↦ hX _)
      (fun _ ↦ b) (fun _ _ _ eq ↦ hi _ (congrArg Subtype.val eq))
      (fun _ ↦ Subset.rfl) (fun y ↦ ⟨0, sur y⟩) (hX n) a
    exact ⟨v, ContinuousLinearMap.ext fun x ↦ congrArg Subtype.val (DFunLike.congr_fun hv x)⟩
  choose j hj using step
  have hem (n : ℕ) : IsEmbedding (j n) := by
    refine frechetEmbedding (hX n) (hX _) _ ?_ ?_
    · intro a b hab
      exact hi n (((DFunLike.congr_fun (hj n) a).symm.trans
        (congrArg (u (n+1)) hab)).trans (DFunLike.congr_fun (hj n) b))
    · have eq : range (j n) = u (n+1) ⁻¹' range (u n) := by
        ext x
        constructor
        · rintro ⟨y,rfl⟩
          exact ⟨y, (DFunLike.congr_fun (hj n) y).symm⟩
        · rintro ⟨y,hy⟩
          exact ⟨y, hi _ ((DFunLike.congr_fun (hj n) y).trans hy)⟩
      rw [eq]
      exact (hc n).preimage (u _).continuous
  have hlim : IsInjectiveLCLimit j u := by
    refine ⟨hi, hj, cover, ?_⟩
    obtain ⟨_, Y, _, _, _, hY, _, i, h⟩ := lf
    have hP : WithSeminorms (Subtype.val :
        {p : Seminorm ℂ E // ∀ n, Continuous (p ∘ (i n).toLinearMap)} → _) := ⟨h.topology_eq⟩
    have eq : (fun p : Seminorm ℂ E ↦ ∀ n, Continuous (p ∘ (u n).toLinearMap)) =
        (fun p : Seminorm ℂ E ↦ ∀ n, Continuous (p ∘ (i n).toLinearMap)) := by
      funext p
      apply propext
      constructor
      · intro hp n
        obtain ⟨k, v, hv⟩ := frechet_factorization hX u hi hr cover (hY n) (i n)
        exact hv ▸ (hp k).comp v.continuous
      · intro hp k
        exact (hP.continuous_seminorm ⟨p,hp⟩).comp (u k).continuous
    unfold locallyConvexFinalTopology
    rw [eq]
    exact hP.withSeminorms_eq
  let (n : ℕ) : IsTopologicalAddGroup (X n) := (hX n).1
  let (n : ℕ) : PolynormableSpace ℂ (X n) := (hX n).2.1
  have hf n := (embedded_frechet_range (u n) (hlim.isEmbedding_stage hem n) (hX n)).2
  exact strictLF_of_countable_frechet_cover lf R hc hf cover

end ClosedImages

/-- Strictness now follows if each of these explicitly defined fixed subspaces is
Fréchet in its induced topology. -/
theorem strictLF_of_fixedStages
    (h : ∀ H : OpenSubgroup (IntegralUnits F S), IsFrechetTVS (fixedStage H)) :
    IsStrictLFSpace (SLocalAdelicThetaSpace F S) := by
  obtain ⟨H, _, _, hcover⟩ := theta_fixedStage_cover (F := F) (S := S)
  exact strictLF_of_countable_frechet_cover sLocalAdelicThetaSpace_lf
    (fun n ↦ fixedStage (H n)) (fun n ↦ fixedStage_closed _) (fun n ↦ h _) hcover

/-- It suffices to parametrize each fixed stage by a continuous linear map from a
Fréchet space. Its kernel may be nonzero and no continuous inverse is assumed. -/
theorem strictLF_of_fixedStage_parametrizations {X : OpenSubgroup (IntegralUnits F S) → Type*}
    [∀ H, AddCommGroup (X H)] [∀ H, Module ℂ (X H)] [∀ H, TopologicalSpace (X H)]
    (hX : ∀ H, IsFrechetTVS (X H)) (p : ∀ H, X H →L[ℂ] SLocalAdelicThetaSpace F S)
    (hp : ∀ H, (p H).toLinearMap.range = fixedStage H) :
    IsStrictLFSpace (SLocalAdelicThetaSpace F S) := by
  let : T2Space (SLocalAdelicThetaSpace F S) :=
    sLocalAdelicThetaSpace_t2_of_isClosed sLocalAdelicTheta_ker_isClosed
  obtain ⟨H, hanti, _, hcover⟩ := theta_fixedStage_cover (F := F) (S := S)
  let K n := (p (H n)).ker
  let u n := (K n).liftQL (p (H n)) le_rfl
  have hr (n : ℕ) : range (u n) = (fixedStage (H n) : Set _) := by
    rw [← hp]
    exact ((K n).mkQ_surjective.range_comp (u n)).symm
  apply strictLF_of_closed_frechet_images sLocalAdelicThetaSpace_lf
    (fun n ↦ isFrechetTVS_quotient (hX (H n)) (K n) (p _).isClosed_ker) u
    (fun n ↦ LinearMap.ker_eq_bot.mp ((K n).ker_liftQ_eq_bot' (p _).toLinearMap rfl))
  · intro n
    rw [hr,hr]
    exact fun _ hx k hk ↦ hx k (hanti n.le_succ hk)
  · intro n
    rw [hr]
    exact fixedStage_closed _
  · intro x
    obtain ⟨n,hn⟩ := hcover x
    exact ⟨n, (hr n).symm ▸ hn⟩

local notation "ArchTest" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
local notation "FiniteTest" => SchwartzBruhat (Multiplicative (FinitePlaceProduct F S))
local notation "Test" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Theta" => SLocalAdelicThetaSpace F S

/-- The finite variables of each actual S-adelic test form a locally constant,
compactly supported function valued in the archimedean Schwartz space. -/
theorem archCoefficients (f : Test) :
    ∃ g : FinitePlaceProduct F S → ArchTest, IsLocallyConstant g ∧ HasCompactSupport g ∧
      ∀ y : SAdeleRing F S, f (Multiplicative.ofAdd y) = g y.2 (Multiplicative.ofAdd y.1) := by
  let A := Multiplicative (InfiniteAdeleRing F)
  let : T2Space A := inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology A := inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  let : TotallyDisconnectedSpace (Multiplicative (FinitePlaceProduct F S)) :=
    inferInstanceAs (TotallyDisconnectedSpace ((w : S) → w.val.adicCompletion F))
  obtain ⟨e, he⟩ := kernel_with_finitePlaceProduct F (G := A) S (archFiniteProductEquiv F S)
  obtain ⟨z,rfl⟩ := e.surjective f
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨hl,hc⟩ := schwartzBruhat_locallyConstant_compactSupport (finitePlaceProduct_compact_subset_subgroup F S) b
    let t (x : FinitePlaceProduct F S) := b (Multiplicative.ofAdd x)
    refine ⟨fun x ↦ t x • a, hl.comp (fun c ↦ c • a), ?_, fun y ↦ ?_⟩
    · exact HasCompactSupport.smul_right (f' := fun _ ↦ a) (show HasCompactSupport t from hc)
    · exact (he a b (Multiplicative.ofAdd y)).trans (mul_comm _ _)
  | add x y hx hy =>
    obtain ⟨u,hu,huc,heU⟩ := hx
    obtain ⟨v,hv,hvc,heV⟩ := hy
    refine ⟨u + v, hu.comp₂ hv (· + ·), huc.add hvc, fun z ↦ ?_⟩
    exact (congrArg (fun w : Test ↦ w (Multiplicative.ofAdd z)) (e.map_add x y)).trans
      (congrArg₂ (· + ·) (heU z) (heV z))

/-- For a class fixed at a given level, the coefficient function can itself be
chosen invariant at that level. -/
theorem fixedArchCoefficients (H : OpenSubgroup (IntegralUnits F S)) {x : Theta} (hx : x ∈ fixedStage H) :
    ∃ f : Test, ∃ g : FinitePlaceProduct F S → ArchTest, (sLocalAdelicTheta F S).ker.mkQ f = x ∧
      IsLocallyConstant g ∧ HasCompactSupport g ∧
      (∀ y : SAdeleRing F S, f (Multiplicative.ofAdd y) = g y.2 (Multiplicative.ofAdd y.1)) ∧
      ∀ k ∈ H, ∀ y, g ((finiteLocalUnit k).val * y) = g y := by
  obtain ⟨f,hq,hfix⟩ := fixedStage_lifts H hx
  obtain ⟨g,hl,hc,he⟩ := archCoefficients f
  refine ⟨f,g,hq,hl,hc,he, fun k hk y ↦ Subtype.ext (funext fun z ↦ ?_)⟩
  have hh := congrArg (fun t : Test ↦ t (Multiplicative.ofAdd (z.toAdd,y))) (hfix k⁻¹ (H.inv_mem hk))
  rw [schwartzBruhatUnitTranslate_apply, map_inv, inv_inv] at hh
  have hv := he ((finiteUnitIdele k).val * (z.toAdd,y))
  have hz : (finiteUnitIdele k).val.1 * z.toAdd = z.toAdd := one_mul _
  exact (congrArg (g ((finiteLocalUnit k).val * y)) (congrArg Multiplicative.ofAdd hz.symm)).trans
    (hv.symm.trans (hh.trans (he (z.toAdd,y))))


/-- After fixing any open subgroup of the finite multiplicative factors, principal
S-unit translation reduces every finite idele coset to a common finite list. The
archimedean component of the translating S-unit remains part of the translation. -/
theorem finiteCosetRepresentatives {F : Type*} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (H : OpenSubgroup (FinitePlaceProduct F S)ˣ) :
    let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) (FinitePlaceProduct F S)
    ∃ R : Finset ((FinitePlaceProduct F S)ˣ ⧸ H.toSubgroup),
      ∀ d : (FinitePlaceProduct F S)ˣ, ∃ u : (SAdeleRing F S)ˣ,
        (QuotientGroup.mk u : SIdeleQuotient F S) = 1 ∧
        QuotientGroup.mk ((e u).2 * d) ∈ R := by
  classical
  intro e
  let π : (SAdeleRing F S)ˣ →* SIdeleQuotient F S := QuotientGroup.mk' _
  let key (y : (SAdeleRing F S)ˣ) := (QuotientGroup.mk (e y).2 : (FinitePlaceProduct F S)ˣ ⧸ H.toSubgroup)
  obtain ⟨C,hC,hrep⟩ := sLocalTheta_exists_compact_representatives F S
  have hfin : (key '' C).Finite :=
    (hC.image (QuotientGroup.continuous_mk.comp (continuous_snd.comp e.continuous))).finite_of_discrete
  refine ⟨hfin.toFinset, fun d ↦ ?_⟩
  let y := e.symm (1,d)
  let t := sIdeleNorm F S y
  let a := Units.map (adeleProjection F S).toMonoidHom (canonicalIdeleNormSection F t)
  have ha : sIdeleNorm F S a = t := sLocalTheta_radial_norm F S t
  have haf : (e a).2 = 1 := by
    apply Units.ext
    funext w
    exact congrArg (fun z : FiniteAdeleRing (𝓞 F) F ↦ z w.val) (canonicalIdeleNormSection_finite F t)
  let z := a⁻¹ * y
  have hz : sIdeleQuotientNorm F S (π z) = 1 := by
    change sIdeleQuotientNorm F S (QuotientGroup.mk (a⁻¹ * y)) = 1
    rw [sIdeleQuotientNorm_mk, map_mul, map_inv, ha, inv_mul_cancel]
  obtain ⟨k,hk,he⟩ := hrep (π z) hz
  have hkey : (e z).2 = d := by
    simp only [z, map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, haf, inv_one, one_mul,
      y, e.apply_symm_apply]
  refine ⟨k / z, ?_, hfin.mem_toFinset.mpr ⟨k,hk,?_⟩⟩
  · change π (k / z) = 1
    simp only [map_div, show π k = π z from he, div_self']
  · change QuotientGroup.mk (e k).2 = QuotientGroup.mk ((e (k / z)).2 * d)
    rw [map_div, Prod.snd_div, hkey, div_mul_cancel]

#print axioms finiteCosetRepresentatives

private theorem sameTranslateOfCoset {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (H : OpenSubgroup Rˣ) (b : SchwartzBruhat (Multiplicative R))
    (hb : ∀ h ∈ H, schwartzBruhatUnitTranslate h b = b)
    {c d : Rˣ} (he : (QuotientGroup.mk c : Rˣ ⧸ H.toSubgroup) = QuotientGroup.mk d) :
    schwartzBruhatUnitTranslate c b = schwartzBruhatUnitTranslate d b := by
  let r := unitTranslateEnd (R := R)
  have h : r (c / d) b = b := hb _ (QuotientGroup.eq_iff_div_mem.mp he)
  calc r c b = r (d * (c / d)) b := by rw [mul_comm, div_mul_cancel]
       _ = r d (r (c / d) b) := DFunLike.congr_fun (r.map_mul _ _) b
       _ = r d b := congrArg (r d) h

private theorem principalClass (u : (SAdeleRing F S)ˣ)
    (hu : (QuotientGroup.mk u : SIdeleQuotient F S) = 1) (f : Test) :
    (sLocalAdelicTheta F S).ker.mkQ (schwartzBruhatUnitTranslate u f) =
      (sLocalAdelicTheta F S).ker.mkQ f := by
  simp only [Submodule.mkQ_apply, Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]
  apply ContinuousMap.ext
  intro x
  refine (localTheta_translate_apply (F := F) (S := S) u x f).trans
    ((sLocalAdelicTheta_factorsThrough F S f) ?_)
  change (QuotientGroup.mk' _ (u⁻¹ * x) : SIdeleQuotient F S) = QuotientGroup.mk' _ x
  rw [map_mul,map_inv]
  change (QuotientGroup.mk u : SIdeleQuotient F S)⁻¹ * _ = _
  rw [hu,inv_one,one_mul]

/-- All multiplicative translates of a fixed finite test, paired with arbitrary
archimedean Schwartz tests, require only finitely many finite templates in the
actual theta quotient. Each S-unit also translates the archimedean coefficient. -/
theorem finiteTranslateTemplates (H : OpenSubgroup (FinitePlaceProduct F S)ˣ)
    (b : FiniteTest) (hb : ∀ h ∈ H, schwartzBruhatUnitTranslate h b = b) :
    ∃ T : Finset FiniteTest, ∀ (d : (FinitePlaceProduct F S)ˣ) (a : ArchTest) (f : Test),
      (∀ y : SAdeleRing F S, f (Multiplicative.ofAdd y) =
        a (Multiplicative.ofAdd y.1) * schwartzBruhatUnitTranslate d b (Multiplicative.ofAdd y.2)) →
      ∃ c ∈ T, ∃ a' : ArchTest, ∃ f' : Test,
        (sLocalAdelicTheta F S).ker.mkQ f = (sLocalAdelicTheta F S).ker.mkQ f' ∧
        ∀ y : SAdeleRing F S, f' (Multiplicative.ofAdd y) =
          a' (Multiplicative.ofAdd y.1) * c (Multiplicative.ofAdd y.2) := by
  classical
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) (FinitePlaceProduct F S)
  obtain ⟨R,hR⟩ := finiteCosetRepresentatives S H
  let cell (q : (FinitePlaceProduct F S)ˣ ⧸ H.toSubgroup) := schwartzBruhatUnitTranslate q.out b
  refine ⟨R.image cell, fun d a f hf ↦ ?_⟩
  obtain ⟨u,hu,hm⟩ := hR d
  let s := (e u).2 * d
  let q : (FinitePlaceProduct F S)ˣ ⧸ H.toSubgroup := QuotientGroup.mk s
  have hcell : schwartzBruhatUnitTranslate s b = cell q :=
    sameTranslateOfCoset H b hb (Quotient.out_eq' q).symm
  refine ⟨cell q, Finset.mem_image_of_mem cell hm, schwartzBruhatUnitTranslate (e u).1 a,
    schwartzBruhatUnitTranslate u f, (principalClass u hu f).symm, fun y ↦ ?_⟩
  rw [← hcell]
  change f (Multiplicative.ofAdd (u.inv * y)) = _ * _
  rw [hf]
  apply congrArg₂ (· * ·) rfl
  change b (Multiplicative.ofAdd (d.inv * ((e u).2.inv * y.2))) =
    b (Multiplicative.ofAdd ((d.inv * (e u).2.inv) * y.2))
  rw [mul_assoc]

#print axioms finiteTranslateTemplates

/-- Tensor an archimedean test with a fixed finite-place test, then take its class. -/
theorem theta_tensor_slice (b : FiniteTest) :
    ∃ L : ArchTest →L[ℂ] Theta, ∀ a, ∃ f : Test,
      (sLocalAdelicTheta F S).ker.mkQ f = L a ∧
      ∀ x : SAdeleRing F S, f (Multiplicative.ofAdd x) =
        a (Multiplicative.ofAdd x.1) * b (Multiplicative.ofAdd x.2) := by
  let A := Multiplicative (InfiniteAdeleRing F)
  let : T2Space A := inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology A := inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  obtain ⟨e, he⟩ := kernel_with_finitePlaceProduct F (G := A) S (archFiniteProductEquiv F S)
  let T := (TensorProduct.mk ℂ ArchTest FiniteTest).flip b
  let J : ArchTest →L[ℂ] InductiveTensor ArchTest FiniteTest := ⟨T,
    (withGeneratingSeminorms_spec (ArchTest ⊗[ℂ] FiniteTest)
      (fun p : {p : Seminorm ℂ (ArchTest ⊗[ℂ] FiniteTest) //
        (∀ x : ArchTest, Continuous (fun y : FiniteTest ↦ p (x ⊗ₜ[ℂ] y))) ∧
        (∀ y : FiniteTest, Continuous (fun x : ArchTest ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val)
      ).continuous_of_continuous_comp T (fun p ↦ p.2.2 b)⟩
  exact ⟨(sLocalAdelicTheta F S).ker.mkQL.comp (e.toContinuousLinearMap.comp J),
    fun a ↦ ⟨e (J a), rfl, fun x ↦ he a b (Multiplicative.ofAdd x)⟩⟩

/-- At each open-subgroup level it suffices to give a finite list of finite-place tests
whose tensor slices span all fixed theta classes. The slices can also produce classes
outside the level. No embedding, continuity of a fold, or closed-range assertion is
required of the proposed list. -/
theorem strictLF_of_finite_templates
    (gen : ∀ H : OpenSubgroup (IntegralUnits F S), ∃ n : ℕ, ∃ b : Fin n → FiniteTest,
      ∀ x ∈ fixedStage H, ∃ a : Fin n → ArchTest, ∃ f : Fin n → Test,
        (∀ i, ∀ y : SAdeleRing F S, f i (Multiplicative.ofAdd y) =
          a i (Multiplicative.ofAdd y.1) * b i (Multiplicative.ofAdd y.2)) ∧
        x = ∑ i, (sLocalAdelicTheta F S).ker.mkQ (f i)) :
    IsStrictLFSpace Theta := by
  classical
  let V := SchwartzMap (mixedEmbedding.mixedSpace F) ℂ
  let A := (archimedeanSchwartzBruhat_equiv (F := F)).choose
  let : PolynormableSpace ℂ V := (schwartz_withSeminorms ℂ _ _).toPolynormableSpace
  let : CompleteSpace V := completeSpace_schwartzMap
  have : (uniformity V).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero V]
    infer_instance
  let : MetrizableSpace V := UniformSpace.metrizableSpace
  choose n b hb using gen
  let W (H : OpenSubgroup (IntegralUnits F S)) := Fin (n H) → V
  let P (H : OpenSubgroup (IntegralUnits F S)) : W H →L[ℂ] Theta := ∑ i,
    ((theta_tensor_slice (b H i)).choose.comp A.toContinuousLinearMap).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ ↦ V) i)
  have covers (H : OpenSubgroup (IntegralUnits F S)) : fixedStage H ≤ (P H).toLinearMap.range := by
    intro x hx
    obtain ⟨a,f,hf,hx'⟩ := hb H x hx
    refine ⟨fun i ↦ A.symm (a i), hx' ▸ ?_⟩
    change P H (fun i ↦ A.symm (a i)) = ∑ i, (sLocalAdelicTheta F S).ker.mkQ (f i)
    simp only [P, sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    apply Finset.sum_congr rfl
    intro i _
    obtain ⟨g,hg,hval⟩ := (theta_tensor_slice (b H i)).choose_spec (a i)
    have eq : g = f i := Subtype.ext (funext fun z ↦ (hval z.toAdd).trans (hf i z.toAdd).symm)
    change (theta_tensor_slice (b H i)).choose (A (A.symm (a i))) = _
    rw [A.apply_symm_apply]
    exact hg.symm.trans (congrArg _ eq)
  let D H := (fixedStage H).comap (P H).toLinearMap
  have hclosed H : IsClosed (D H : Set (W H)) := (fixedStage_closed H).preimage (P H).continuous
  let A' H := (P H).comp (D H).subtypeL
  apply strictLF_of_fixedStage_parametrizations (X := fun H ↦ D H) _ A'
  · intro H
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      exact z.property
    · intro hx
      obtain ⟨z,hz⟩ := covers H hx
      have hmem : (P H) z ∈ fixedStage H := by rw [show (P H) z = x from hz]; exact hx
      exact ⟨⟨z,hmem⟩, hz⟩
  · intro H
    apply frechet_of_closed_embedding (D H).subtypeL (hclosed H).isClosedEmbedding_subtypeVal
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance

/-- The map obtained by tensoring with a particular finite test. -/
def tensorClass (b : FiniteTest) : ArchTest →L[ℂ] Theta := (theta_tensor_slice b).choose

/-- All that remains is a statement about spanning by translations: at a fixed level,
finitely many seed functions may be translated by *arbitrary finite ideles*. The
quotient calculation above then reduces these to finitely many actual tensor slices. -/
theorem strictLF_of_finitely_many_orbits
    (gen : ∀ H : OpenSubgroup (IntegralUnits F S), ∃ B : Finset FiniteTest,
      (∀ b ∈ B, ∃ U : OpenSubgroup (FinitePlaceProduct F S)ˣ,
        ∀ h ∈ U, schwartzBruhatUnitTranslate h b = b) ∧
      fixedStage H ≤ ⨆ b : B, ⨆ d : (FinitePlaceProduct F S)ˣ,
        (tensorClass (schwartzBruhatUnitTranslate d b.val)).toLinearMap.range) :
    IsStrictLFSpace Theta := by
  classical
  apply strictLF_of_finite_templates
  intro H
  obtain ⟨B, hB, hspan⟩ := gen H
  choose U hU using fun b : B ↦ hB b.val b.property
  choose T hT using fun b : B ↦ finiteTranslateTemplates (U b) b.val (hU b)
  let all := Finset.univ.biUnion T
  let e := Fintype.equivFin ↥all
  let bs (i : Fin (Fintype.card ↥all)) := (e.symm i).val
  let P : (Fin (Fintype.card ↥all) → ArchTest) →ₗ[ℂ] Theta :=
    ∑ i, (tensorClass (bs i)).toLinearMap.comp (LinearMap.proj i)
  have term (i : Fin (Fintype.card ↥all)) (a : ArchTest) : tensorClass (bs i) a ∈ P.range := by
    refine ⟨Pi.single i a, ?_⟩
    change (∑ j, ((tensorClass (bs j)).toLinearMap.comp (LinearMap.proj j))) (Pi.single i a) = _
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, ContinuousLinearMap.coe_coe]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, map_zero]
    · simp
  have hcover : fixedStage H ≤ P.range := hspan.trans (iSup_le fun b ↦ iSup_le fun d ↦ by
    rintro _ ⟨a,rfl⟩
    obtain ⟨f,hf,hval⟩ := (theta_tensor_slice (schwartzBruhatUnitTranslate d b.val)).choose_spec a
    obtain ⟨c,hc,a',f',he,hm⟩ := hT b d a f hval
    have hmem : c ∈ all := Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,hc⟩
    let i := e ⟨c,hmem⟩
    have eqb : bs i = c := congrArg Subtype.val (e.symm_apply_apply ⟨c,hmem⟩)
    obtain ⟨z,hz,hev⟩ := (theta_tensor_slice c).choose_spec a'
    have hzf : z = f' := Subtype.ext (funext fun y ↦ (hev y.toAdd).trans (hm y.toAdd).symm)
    have h := term i a'
    rw [eqb] at h
    exact (show tensorClass (schwartzBruhatUnitTranslate d b.val) a = tensorClass c a' from
      hf.symm.trans (he.trans ((congrArg _ hzf.symm).trans hz))) ▸ h)
  refine ⟨_,bs,fun x hx ↦ ?_⟩
  obtain ⟨a,ha⟩ := hcover hx
  choose f hf he using fun i ↦ (theta_tensor_slice (bs i)).choose_spec (a i)
  refine ⟨a,f,he,ha ▸ ?_⟩
  change (∑ i, ((tensorClass (bs i)).toLinearMap.comp (LinearMap.proj i))) a = _
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, ContinuousLinearMap.coe_coe]
  exact Finset.sum_congr rfl fun i _ ↦ (hf i).symm

/-- Every finite-place test has an open stabilizer in the full finite idele group. -/
theorem finiteTestStabilizer (b : FiniteTest) :
    ∃ U : OpenSubgroup (FinitePlaceProduct F S)ˣ, ∀ h ∈ U, schwartzBruhatUnitTranslate h b = b := by
  let D := FinitePlaceProduct F S
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (v : S) : LocallyCompactSpace (v.val.adicCompletion F)ˣ :=
    IsOpenUnits.isOpenEmbedding_unitsVal.locallyCompactSpace
  let : LocallyCompactSpace Dˣ :=
    (ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let : TotallyDisconnectedSpace (Multiplicative D) :=
    inferInstanceAs (TotallyDisconnectedSpace ((w : S) → w.val.adicCompletion F))
  obtain ⟨hl,hc⟩ := schwartzBruhat_locallyConstant_compactSupport (finitePlaceProduct_compact_subset_subgroup F S) b
  let r := unitTranslateEnd (R := D)
  have hloc : IsLocallyConstant (fun h : Dˣ ↦ r h b) := by
    have he := locallyConstant_unit_family (id : Dˣ → Dˣ) continuous_id
      (fun y ↦ b (Multiplicative.ofAdd y)) hl hc
    exact (IsLocallyConstant.iff_eventually_eq _).mpr fun h ↦
      (he.eventually_eq h).mono fun k hk ↦ Subtype.ext hk
  let U : Subgroup Dˣ :=
    { carrier := {h | r h b = b}
      one_mem' := by change r 1 b = b; rw [map_one]; rfl
      mul_mem' := fun {h k} hh hk ↦ (DFunLike.congr_fun (r.map_mul h k) b).trans
        ((congrArg (r h) hk).trans hh)
      inv_mem' := fun {h} hh ↦ by
        calc r h⁻¹ b = r h⁻¹ (r h b) := congrArg (r h⁻¹) hh.symm
             _ = r (h⁻¹ * h) b := (DFunLike.congr_fun (r.map_mul h⁻¹ h) b).symm
             _ = b := by rw [inv_mul_cancel,map_one]; rfl }
  exact ⟨⟨U,hloc.isOpen_fiber b⟩, fun _ hh ↦ hh⟩

/-- The only additional hypothesis needed to deduce the target on the actual quotient
is the algebraic spanning property for every fixed level. -/
theorem strictLF_of_orbit_spans
    (gen : ∀ H : OpenSubgroup (IntegralUnits F S), ∃ B : Finset FiniteTest,
      fixedStage H ≤ ⨆ b : B, ⨆ d : (FinitePlaceProduct F S)ˣ,
        (tensorClass (schwartzBruhatUnitTranslate d b.val)).toLinearMap.range) :
    IsStrictLFSpace Theta := by
  apply strictLF_of_finitely_many_orbits
  intro H
  obtain ⟨B,hB⟩ := gen H
  exact ⟨B,fun b _ ↦ finiteTestStabilizer b,hB⟩

#print axioms finiteTestStabilizer
#print axioms strictLF_of_orbit_spans

#print axioms strictLF_of_finitely_many_orbits

#print axioms strictLF_of_finite_templates
#print axioms strictLF_of_closed_frechet_images
#print axioms strictLF_of_fixedStage_parametrizations
#print axioms finiteTestOrbit
#print axioms fixedStage_lifts
#print axioms finiteThetaOrbit
#print axioms fixedStage_closed
#print axioms theta_fixedStage_cover
#print axioms strictLF_of_fixedStages

end MasulloI123Exact
