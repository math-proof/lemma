import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {k : Type u} [Field k]

private noncomputable abbrev chartAlgebra
  {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of k))
  (U : X.Opens) : Algebra k (X.presheaf.obj (op U)) :=
  ((f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
private lemma chart_finiteType
  {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  {U : X.Opens}
  -- given
  (hU : IsAffineOpen U) :
  -- imply
  let _ := chartAlgebra f U
  Algebra.FiniteType k (X.presheaf.obj (op U)) := by
  -- proof
  apply (f.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
  apply RingHom.FiniteType.of_surjective _
  apply (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
private lemma chart_isNoetherianRing
  {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  {U : X.Opens}
  -- given
  (hU : IsAffineOpen U) :
  -- imply
  IsNoetherianRing (X.presheaf.obj (op U)) := by
  -- proof
  let _ := chartAlgebra f U
  let _ := chart_finiteType f hU
  apply Algebra.FiniteType.isNoetherianRing k (X.presheaf.obj (op U))
private lemma primeIdealOf_fromSpec
  {X : (Scheme : Type (u + 1))} {U : X.Opens} (hU : IsAffineOpen U)
  (q : PrimeSpectrum (X.presheaf.obj (op U)))
  -- given
  (h : hU.fromSpec q ∈ U) :
  -- imply
  hU.primeIdealOf ⟨hU.fromSpec q, h⟩ = q := by
  -- proof
  apply hU.fromSpec.isOpenEmbedding.injective
  apply hU.fromSpec_primeIdealOf ⟨hU.fromSpec q, h⟩
private lemma ringKrullDim_stalk_eq_height
  {X : (Scheme : Type (u + 1))} {U : X.Opens} (hU : IsAffineOpen U)
  (x : X)
  -- given
  (hx : x ∈ U) :
  -- imply
  ringKrullDim (X.presheaf.stalk x) = (hU.primeIdealOf ⟨x, hx⟩).asIdeal.height := by
  -- proof
  let _ := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  let _ := hU.isLocalization_stalk ⟨x, hx⟩
  apply IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hx⟩).asIdeal (X.presheaf.stalk x)
variable {G P : (Scheme : Type (u + 1))} (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))
private lemma exists_isGenericPoint
  [UniversallyOpen f] [GeometricallyIrreducible f] [Flat f]
  (w : P) :
  -- imply
  ∃ ζ : ↥(pullback f p), IsGenericPoint ζ ((pullback.snd f p).base ⁻¹' closure ({w} : Set P)) ∧ (pullback.snd f p).base ζ = w := by
  -- proof
  set g := pullback.snd f p with hg
  have hT : IsIrreducible ((g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P)) :=
    g.isIrreducible_preimage g.isOpenMap isIrreducible_singleton.closure
  have hTc : IsClosed ((g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P)) :=
    isClosed_closure.preimage g.continuous
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober hT hTc
  refine ⟨ζ, hζ, ?_⟩
  have hζT : ζ ∈ (g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P) := hζ.mem
  have hwy : w ⤳ g.base ζ := Iff.mpr specializes_iff_mem_closure hζT
  have hgen : GeneralizingMap g := Flat.generalizingMap g
  obtain ⟨ζ', hζ'ζ, hζ'w⟩ := hgen hwy
  have hζ'T : ζ' ∈ (g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P) := by
    show g.base ζ' ∈ closure ({w} : Set P)
    rw [hζ'w]
    apply subset_closure
    rfl
  have hζζ' : ζ ⤳ ζ' := hζ.specializes hζ'T
  have : ζ' = ζ := (hζ'ζ.antisymm hζζ').eq
  rwa [← this]
variable {G P : (Scheme : Type (u + 1))} (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))
private lemma height_eq
  [Flat f] [LocallyOfFiniteType f] [LocallyOfFiniteType p]
  (w : P)
  (ζ : ↥(pullback f p))
  (hζ : IsGenericPoint ζ ((pullback.snd f p).base ⁻¹' closure ({w} : Set P)))
  (hζw : (pullback.snd f p).base ζ = w)
  {V : P.Opens} (hV : IsAffineOpen V) (hwV : w ∈ V)
  {U : (pullback f p).Opens} (hU : IsAffineOpen U) (hζU : ζ ∈ U)
  -- given
  (hUV : U ≤ ((TopologicalSpace.Opens.map (pullback.snd f p).base).obj V)) :
  -- imply
  (hU.primeIdealOf ⟨ζ, hζU⟩).asIdeal.height = (hV.primeIdealOf ⟨w, hwV⟩).asIdeal.height := by
  -- proof
  set g : pullback f p ⟶ P := pullback.snd f p with hg
  let φ : (P.presheaf.obj (op V)) →+* ((pullback f p).presheaf.obj (op U)) := (g.appLE V U hUV).hom
  have hφ : φ.Flat :=
    HasRingHomProperty.appLE @Flat g (inferInstance : Flat g) ⟨V, hV⟩ ⟨U, hU⟩ hUV
  let _ : Algebra (P.presheaf.obj (op V)) ((pullback f p).presheaf.obj (op U)) := φ.toAlgebra
  let _ : Module.Flat (P.presheaf.obj (op V)) ((pullback f p).presheaf.obj (op U)) := hφ
  let _ : Algebra.HasGoingDown (P.presheaf.obj (op V)) ((pullback f p).presheaf.obj (op U)) := inferInstance
  let _ : IsNoetherianRing (P.presheaf.obj (op V)) := chart_isNoetherianRing p hV
  let _ : IsNoetherianRing ((pullback f p).presheaf.obj (op U)) := chart_isNoetherianRing (pullback.fst f p ≫ f) hU
  set Q : PrimeSpectrum ((pullback f p).presheaf.obj (op U)) := hU.primeIdealOf ⟨ζ, hζU⟩ with hQ
  set pw : PrimeSpectrum (P.presheaf.obj (op V)) := hV.primeIdealOf ⟨w, hwV⟩ with hpw
  have hcomap : ∀ q : PrimeSpectrum ((pullback f p).presheaf.obj (op U)), hV.fromSpec (PrimeSpectrum.comap φ q) = g.base (hU.fromSpec q) := by
    intro q
    have h1 := IsAffineOpen.SpecMap_appLE_fromSpec g hV hU hUV
    have h2 := congrArg (fun h => h.base q) h1
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
    rwa [Spec.map_apply] at h2
  have hmemU : ∀ q : PrimeSpectrum ((pullback f p).presheaf.obj (op U)), hU.fromSpec q ∈ U := fun q => by
    have := hU.range_fromSpec ▸ Set.mem_range_self (f := hU.fromSpec) q
    apply this
  have hmemV : ∀ q : PrimeSpectrum (P.presheaf.obj (op V)), hV.fromSpec q ∈ V := fun q => by
    have := hV.range_fromSpec ▸ Set.mem_range_self (f := hV.fromSpec) q
    apply this
  have hζQ : hU.fromSpec Q = ζ := hU.fromSpec_primeIdealOf ⟨ζ, hζU⟩
  have hwpw : hV.fromSpec pw = w := hV.fromSpec_primeIdealOf ⟨w, hwV⟩
  have hunder : PrimeSpectrum.comap φ Q = pw := by
    have h1 : hV.fromSpec (PrimeSpectrum.comap φ Q) = w := by rw [hcomap, hζQ, hζw]
    have h2 := primeIdealOf_fromSpec hV (PrimeSpectrum.comap φ Q) (hmemV _)
    rw [← h2]
    have : (⟨hV.fromSpec (PrimeSpectrum.comap φ Q), hmemV _⟩ : V) = ⟨w, hwV⟩ := Subtype.ext h1
    rw [this]
  let hlies : Q.asIdeal.LiesOver pw.asIdeal := by
    refine ⟨?_⟩
    rw [Ideal.under_def]
    have := congrArg PrimeSpectrum.asIdeal hunder
    have h__af := this.symm
    simp [PrimeSpectrum.comap_asIdeal] at h__af
    apply h__af
  have hmin : ∀ Q' : PrimeSpectrum ((pullback f p).presheaf.obj (op U)), pw.asIdeal.map φ ≤ Q'.asIdeal → Q' ≤ Q → Q' = Q := by
    intro Q' hJ hle
    set ζ' : ↥(pullback f p) := hU.fromSpec Q' with hζ'
    have hζ'ζ : ζ' ⤳ ζ := by
      have := (Iff.mp (PrimeSpectrum.le_iff_specializes _ _) hle).map hU.fromSpec.continuous
      rwa [hζQ] at this
    have hpw' : pw ≤ PrimeSpectrum.comap φ Q' := by
      rwa [← PrimeSpectrum.asIdeal_le_asIdeal, PrimeSpectrum.comap_asIdeal, ← Ideal.map_le_iff_le_comap]
    have hgζ' : g.base ζ' ∈ closure ({w} : Set P) := by
      have := (Iff.mp (PrimeSpectrum.le_iff_specializes _ _) hpw').map hV.fromSpec.continuous
      rw [hwpw, hcomap] at this
      apply Iff.mp specializes_iff_mem_closure this
    have hζ'T : ζ' ∈ (g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P) := hgζ'
    have hζζ' : ζ ⤳ ζ' := hζ.specializes hζ'T
    have heq : ζ' = ζ := (hζ'ζ.antisymm hζζ').eq
    have h1 := primeIdealOf_fromSpec hU Q' (hmemU _)
    rw [← h1]
    have : (⟨hU.fromSpec Q', hmemU _⟩ : U) = ⟨ζ, hζU⟩ := Subtype.ext heq
    rw [this]
  set J : Ideal ((pullback f p).presheaf.obj (op U)) := pw.asIdeal.map (algebraMap (P.presheaf.obj (op V)) ((pullback f p).presheaf.obj (op U))) with hJdef
  have hJφ : J = pw.asIdeal.map φ := rfl
  have hJQ : J ≤ Q.asIdeal := by
    rw [hJdef, Ideal.map_le_iff_le_comap]
    apply le_of_eq (hlies.over.symm ▸ rfl)
  have hfib : (Q.asIdeal.map (Ideal.Quotient.mk J)).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    let hQm : (Q.asIdeal.map (Ideal.Quotient.mk J)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    refine ⟨⟨hQm, bot_le⟩, ?_⟩
    rintro q' ⟨hq', -⟩ hq'le
    let _ := hq'
    let Q' : PrimeSpectrum ((pullback f p).presheaf.obj (op U)) := ⟨q'.comap (Ideal.Quotient.mk J), inferInstance⟩
    have hJQ' : pw.asIdeal.map φ ≤ Q'.asIdeal := by
      show J ≤ q'.comap (Ideal.Quotient.mk J)
      intro x hx
      rw [Ideal.mem_comap, Iff.mpr Ideal.Quotient.eq_zero_iff_mem hx]
      apply q'.zero_mem
    have hQ'Q : Q' ≤ Q := by
      rw [← PrimeSpectrum.asIdeal_le_asIdeal]
      show q'.comap (Ideal.Quotient.mk J) ≤ Q.asIdeal
      intro x hx
      rw [Ideal.mem_comap] at hx
      have hx' : Ideal.Quotient.mk J x ∈ Q.asIdeal.map (Ideal.Quotient.mk J) := hq'le hx
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      rw [Ideal.Quotient.eq, ← neg_sub] at hyx
      have hxy : x - y ∈ Q.asIdeal := hJQ ((neg_mem_iff).mp hyx)
      have := Q.asIdeal.add_mem hxy hy
      simpa using this
    have hEq : Q' = Q := hmin Q' hJQ' hQ'Q
    apply le_of_eq
    symm
    have h1 : q' = (q'.comap (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk J) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q').symm
    rw [h1]
    show Q'.asIdeal.map _ = _
    rw [hEq]
  have hgd := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown pw.asIdeal Q.asIdeal
  rwa [hfib, add_zero] at hgd
private lemma helper_main
  {G P : (Scheme : Type (u + 1))} (f : G ⟶ Spec (CommRingCat.of k))
  (p : P ⟶ Spec (CommRingCat.of k))
  [GeometricallyIrreducible f] [LocallyOfFiniteType f] [LocallyOfFiniteType p]
  (w : P) :
  -- imply
  ∃ ζ : ↥(pullback f p), closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure ({w} : Set P) ∧
    (pullback.snd f p).base ζ = w ∧
    ringKrullDim ((pullback f p).presheaf.stalk ζ) = ringKrullDim (P.presheaf.stalk w) := by
  -- proof
  let _ : Flat f := inferInstance
  let _ : UniversallyOpen f := inferInstance
  obtain ⟨ζ, hζ, hζw⟩ := exists_isGenericPoint f p w
  refine ⟨ζ, hζ, hζw, ?_⟩
  obtain ⟨V, hV, hwV, -⟩ := exists_isAffineOpen_mem_and_subset (X := P) (x := w) (U := ⊤) trivial
  have hζV : ζ ∈ ((TopologicalSpace.Opens.map (pullback.snd f p).base).obj V) := by
    show (pullback.snd f p).base ζ ∈ V
    rwa [hζw]
  obtain ⟨U, hU, hζU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := pullback f p) (x := ζ) (U := ((TopologicalSpace.Opens.map (pullback.snd f p).base).obj V)) hζV
  rw [ringKrullDim_stalk_eq_height hU ζ hζU, ringKrullDim_stalk_eq_height hV w hwV,
    height_eq f p w ζ hζ hζw hV hwV hU hζU hUV]
/--
[AlgebraicGeometry_exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] {G P : (Scheme : Type (u + 1))} (f : G ⟶ Spec (CommRingCat.of k))
  (p : P ⟶ Spec (CommRingCat.of k))
  [GeometricallyIrreducible f] [LocallyOfFiniteType f] [LocallyOfFiniteType p]
  (w : P) :
  -- imply
  ∃ ζ : ↥(pullback f p), closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure ({w} : Set P) ∧
    (pullback.snd f p).base ζ = w ∧
    ringKrullDim ((pullback f p).presheaf.stalk ζ) = ringKrullDim (P.presheaf.stalk w) :=
  helper_main f p w


-- created on 2026-10-20
