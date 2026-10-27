import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {α : Type*} [TopologicalSpace α]
private lemma isPreirreducible_union_of_isOpen_of_mem
  {s U : Set α}
  (hs : IsPreirreducible s) (hU : IsPreirreducible U) (hUopen : IsOpen U)
  {y : α} (hys : y ∈ s) (hyU : y ∈ U) : IsPreirreducible (s ∪ U) := by
  have key : ∀ w : Set α, IsOpen w → ((s ∪ U) ∩ w).Nonempty → (U ∩ w).Nonempty := by
    rintro w hw ⟨z, hz, hzw⟩
    obtain hzs | hzU := hz
    ·
      obtain ⟨t, hts, htw, htU⟩ := hs w U hw hUopen ⟨z, hzs, hzw⟩ ⟨y, hys, hyU⟩
      exact ⟨t, htU, htw⟩
    · exact ⟨z, hzU, hzw⟩
  rintro a b ha hb hane hbne
  obtain ⟨t, htU, htab⟩ := hU a b ha hb (key a ha hane) (key b hb hbne)
  exact ⟨t, Or.inr htU, htab⟩
private lemma isOpen_irreducibleComponent_of_forall_isPreirreducible_nhd
  (hloc : ∀ y : α, ∃ U : Set α, IsOpen U ∧ y ∈ U ∧ IsPreirreducible U) (x : α) :
  IsOpen (irreducibleComponent x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨U, hUopen, hyU, hUirr⟩ := hloc y
  have hunion : IsPreirreducible (irreducibleComponent x ∪ U) :=
    isPreirreducible_union_of_isOpen_of_mem isIrreducible_irreducibleComponent.2 hUirr hUopen
      hy hyU
  apply Filter.mem_of_superset (hUopen.mem_nhds hyU)
  have heq : irreducibleComponent x ∪ U = irreducibleComponent x :=
    eq_irreducibleComponent hunion Set.subset_union_left
  rw [← heq]
  apply Set.subset_union_right
private lemma connectedComponent_eq_irreducibleComponent_of_forall_isPreirreducible_nhd
  (hloc : ∀ y : α, ∃ U : Set α, IsOpen U ∧ y ∈ U ∧ IsPreirreducible U) (x : α) :
  connectedComponent x = irreducibleComponent x := by
  have hclopen : IsClopen (irreducibleComponent x) :=
    ⟨isClosed_irreducibleComponent,
      isOpen_irreducibleComponent_of_forall_isPreirreducible_nhd hloc x⟩
  apply Set.Subset.antisymm
  · apply isPreconnected_connectedComponent.subset_isClopen hclopen ⟨x, mem_connectedComponent, mem_irreducibleComponent⟩
  · apply isIrreducible_irreducibleComponent.2.isPreconnected.subset_connectedComponent mem_irreducibleComponent
private lemma isPreirreducible_connectedComponent_of_forall_isPreirreducible_nhd
  (hloc : ∀ y : α, ∃ U : Set α, IsOpen U ∧ y ∈ U ∧ IsPreirreducible U) (x : α) :
  IsPreirreducible (connectedComponent x) := by
  rw [connectedComponent_eq_irreducibleComponent_of_forall_isPreirreducible_nhd hloc x]
  apply isIrreducible_irreducibleComponent.2
variable {R : Type u} [CommRing R]
private lemma eq_of_mem_minimalPrimes_of_le_of_isDomain_localizationAtPrime
  {p : Ideal R} [hp : p.IsPrime] (hdom : IsDomain (Localization.AtPrime p))
  {q₁ q₂ : Ideal R} (h₁ : q₁ ∈ minimalPrimes R) (h₂ : q₂ ∈ minimalPrimes R)
  (hle₁ : q₁ ≤ p) (hle₂ : q₂ ≤ p) : q₁ = q₂ := by
  let _ := hdom
  have hq₀p : (Ideal.comap (algebraMap R (Localization.AtPrime p))
      (⊥ : Ideal (Localization.AtPrime p))).IsPrime :=
    Ideal.IsPrime.comap (algebraMap R (Localization.AtPrime p))
  have hker_le : ∀ q : Ideal R, q.IsPrime → q ≤ p →
      Ideal.comap (algebraMap R (Localization.AtPrime p))
        (⊥ : Ideal (Localization.AtPrime p)) ≤ q := by
    intro q hq hqp
    have hdisj : Disjoint ((p.primeCompl : Set R)) ((q : Set R)) :=
      Iff.mpr Set.disjoint_left fun a ha haq => Iff.mp Ideal.mem_primeCompl_iff ha (hqp haq)
    suffices hcm : Ideal.comap (algebraMap R (Localization.AtPrime p)) (Ideal.map (algebraMap R (Localization.AtPrime p)) q) = q by
      apply le_of_le_of_eq (Ideal.comap_mono bot_le) hcm
    apply IsLocalization.under_map_of_isPrime_disjoint p.primeCompl (Localization.AtPrime p) hq hdisj
  have e₁ : q₁ = Ideal.comap (algebraMap R (Localization.AtPrime p)) (⊥ : Ideal (Localization.AtPrime p)) :=
    le_antisymm (h₁.2 ⟨hq₀p, bot_le⟩ (hker_le q₁ h₁.1.1 hle₁)) (hker_le q₁ h₁.1.1 hle₁)
  have e₂ : q₂ = Ideal.comap (algebraMap R (Localization.AtPrime p)) (⊥ : Ideal (Localization.AtPrime p)) :=
    le_antisymm (h₂.2 ⟨hq₀p, bot_le⟩ (hker_le q₂ h₂.1.1 hle₂)) (hker_le q₂ h₂.1.1 hle₂)
  rw [e₁, e₂]
private lemma exists_mem_zeroLocus_minimalPrimes (x : PrimeSpectrum R) :
  ∃ q ∈ minimalPrimes R, x ∈ PrimeSpectrum.zeroLocus (q : Set R) := by
  obtain ⟨q, hq, hle⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := x.asIdeal) bot_le
  exact ⟨q, hq, Iff.mpr (PrimeSpectrum.mem_zeroLocus _ _) (Iff.mpr SetLike.coe_subset_coe hle)⟩
private lemma compl_zeroLocus_eq_biUnion
  (huniq : ∀ q₁ q₂ : Ideal R, q₁ ∈ minimalPrimes R → q₂ ∈ minimalPrimes R →
    ∀ p : Ideal R, p.IsPrime → q₁ ≤ p → q₂ ≤ p → q₁ = q₂)
  {q₀ : Ideal R} (hq₀ : q₀ ∈ minimalPrimes R) :
  (PrimeSpectrum.zeroLocus (q₀ : Set R))ᶜ
    = ⋃ q ∈ minimalPrimes R \ {q₀}, PrimeSpectrum.zeroLocus ((q : Ideal R) : Set R) := by
  ext x
  simp only [Set.mem_compl_iff]
  constructor
  ·
    intro hx
    obtain ⟨q, hq, hxq⟩ := exists_mem_zeroLocus_minimalPrimes x
    suffices hne : q ≠ q₀ by
      apply Set.mem_biUnion (⟨hq, hne⟩ : q ∈ minimalPrimes R \ {q₀}) hxq
    rintro rfl
    apply hx hxq
  ·
    intro hx hx₀
    obtain ⟨q, hq, hxq⟩ := Iff.mp Set.mem_iUnion₂ hx
    apply hq.2 (huniq q q₀ hq.1 hq₀ x.asIdeal x.isPrime (Iff.mp SetLike.coe_subset_coe (Iff.mp (PrimeSpectrum.mem_zeroLocus _ _) hxq)) (Iff.mp SetLike.coe_subset_coe (Iff.mp (PrimeSpectrum.mem_zeroLocus _ _) hx₀)))
private lemma isClopen_zeroLocus_of_mem_minimalPrimes
  [IsNoetherianRing R]
  (huniq : ∀ q₁ q₂ : Ideal R, q₁ ∈ minimalPrimes R → q₂ ∈ minimalPrimes R →
    ∀ p : Ideal R, p.IsPrime → q₁ ≤ p → q₂ ≤ p → q₁ = q₂)
  {q₀ : Ideal R} (hq₀ : q₀ ∈ minimalPrimes R) :
  IsClopen (PrimeSpectrum.zeroLocus (q₀ : Set R)) := by
  refine ⟨PrimeSpectrum.isClosed_zeroLocus _, ?_⟩
  rw [← isClosed_compl_iff, compl_zeroLocus_eq_biUnion huniq hq₀]
  apply Set.Finite.isClosed_biUnion
    (Set.Finite.subset (minimalPrimes.finite_of_isNoetherianRing R) Set.sdiff_subset)
    (fun q _ => PrimeSpectrum.isClosed_zeroLocus _)
private lemma exists_isClopen_isPreirreducible_mem_of_forall_isDomain_localizationAtPrime
  [IsNoetherianRing R]
  (hstalk : ∀ (p : Ideal R) [p.IsPrime], IsDomain (Localization.AtPrime p))
  (x : PrimeSpectrum R) :
  ∃ s : Set (PrimeSpectrum R), IsClopen s ∧ x ∈ s ∧ IsPreirreducible s := by
  have huniq : ∀ q₁ q₂ : Ideal R, q₁ ∈ minimalPrimes R → q₂ ∈ minimalPrimes R →
      ∀ p : Ideal R, p.IsPrime → q₁ ≤ p → q₂ ≤ p → q₁ = q₂ := by
    intro q₁ q₂ h₁ h₂ p hp hle₁ hle₂
    let _ := hp
    exact eq_of_mem_minimalPrimes_of_le_of_isDomain_localizationAtPrime (hstalk p) h₁ h₂ hle₁ hle₂
  obtain ⟨q₀, hq₀, hxq₀⟩ := exists_mem_zeroLocus_minimalPrimes x
  refine ⟨PrimeSpectrum.zeroLocus (q₀ : Set R), isClopen_zeroLocus_of_mem_minimalPrimes huniq hq₀, hxq₀, ?_⟩
  have hq₀p : q₀.IsPrime := hq₀.1.1
  suffices hirr : IsIrreducible (PrimeSpectrum.zeroLocus (q₀ : Set R)) by
    apply hirr.2
  rw [PrimeSpectrum.isIrreducible_zeroLocus_iff]
  rwa [hq₀p.radical]
private lemma isDomain_localizationAtPrime_of_isLocalization
  {R : Type u} [CommRing R]
  (p : Ideal R) [p.IsPrime] (S : Type u) [CommRing S] [Algebra R S]
  [IsLocalization p.primeCompl S] [IsDomain S] :
  IsDomain (Localization.AtPrime p) :=
  MulEquiv.isDomain S
  (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) S).toRingEquiv.toMulEquiv
private lemma exists_primeIdealOf_eq
  {X : (Scheme : Type (u + 1))} {U : X.Opens}
  (hU : IsAffineOpen U) (p : PrimeSpectrum (X.presheaf.obj (op U))) :
    ∃ y : ↥U, hU.primeIdealOf y = p := by
  refine ⟨hU.isoSpec.inv p, ?_⟩
  show hU.isoSpec.hom (hU.isoSpec.inv p) = p
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  simp [Scheme.Hom.id_base]
private lemma exists_isOpen_mem_isPreirreducible_of_forall_isDomain_stalk
  (X : (Scheme : Type (u + 1))) [IsLocallyNoetherian X]
  (hstalk : ∀ x : ↥X, IsDomain (X.presheaf.stalk x)) (x : ↥X) :
  ∃ s : Set ↥X, IsOpen s ∧ x ∈ s ∧ IsPreirreducible s := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) trivial
  let hnoeth : IsNoetherianRing (X.presheaf.obj (op U)) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hloc : ∀ (p : Ideal (X.presheaf.obj (op U))) [p.IsPrime], IsDomain (Localization.AtPrime p) := by
    intro p hp
    obtain ⟨y, hy⟩ := exists_primeIdealOf_eq hU ⟨p, hp⟩
    let hL := hU.isLocalization_stalk y
    let hD := hstalk y.1
    have hdom : IsDomain (Localization.AtPrime (hU.primeIdealOf y).asIdeal) :=
      isDomain_localizationAtPrime_of_isLocalization
        (hU.primeIdealOf y).asIdeal (X.presheaf.stalk y.1)
    rw [hy] at hdom
    apply hdom
  obtain ⟨s, hsclopen, hsmem, hspre⟩ :=
    exists_isClopen_isPreirreducible_mem_of_forall_isDomain_localizationAtPrime
      hloc (hU.primeIdealOf ⟨x, hxU⟩)
  refine ⟨⇑hU.fromSpec '' s, ?_, ?_, ?_⟩
  · exact (Scheme.Hom.isOpenEmbedding hU.fromSpec).isOpenMap _ hsclopen.isOpen
  · exact ⟨hU.primeIdealOf ⟨x, hxU⟩, hsmem, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
  · exact hspre.image _ (Scheme.Hom.continuous hU.fromSpec).continuousOn
private lemma isPreirreducible_connectedComponent_of_forall_isDomain_stalk
  (T : (Scheme : Type (u + 1))) [IsLocallyNoetherian T]
  (hstalk : ∀ x : ↥T, IsDomain (T.presheaf.stalk x)) (x : ↥T) :
  IsPreirreducible (connectedComponent x) :=
  isPreirreducible_connectedComponent_of_forall_isPreirreducible_nhd
  (exists_isOpen_mem_isPreirreducible_of_forall_isDomain_stalk T hstalk) x
/--
[AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.lean)
-/
@[path]
private lemma main
  (X : (Scheme : Type (u + 1))) [IsLocallyNoetherian X] [ConnectedSpace X]
    (h : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IsIntegral X := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hpre : IsPreirreducible (Set.univ : Set X) := by
    rw [← PreconnectedSpace.connectedComponent_eq_univ x]
    exact isPreirreducible_connectedComponent_of_forall_isDomain_stalk X h x
  let _ : IrreducibleSpace X := { isPreirreducible_univ := hpre, toNonempty := ⟨x⟩ }
  let _ : ∀ y : X, _root_.IsReduced (X.presheaf.stalk y) := fun y => inferInstance
  let _ : IsReduced X := isReduced_of_isReduced_stalk X
  apply Iff.mpr (isIntegral_iff_irreducibleSpace_and_isReduced X) ⟨inferInstance, inferInstance⟩


-- created on 2026-10-20
