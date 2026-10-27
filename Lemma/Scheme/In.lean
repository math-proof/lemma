import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma mem_of_closedPoint
  (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {T : (Scheme : Type (u + 1))} (t : T ⟶ Spec (CommRingCat.of R)) [Flat t]
  (V : T.Opens)
  (hVs : ∀ Z ∈ irreducibleComponents (Subtype (fun x : T => t.base x = IsLocalRing.closedPoint R)), ∃ x ∈ Z, x.1 ∈ V)
  (x : T) (hxs : t.base x = IsLocalRing.closedPoint R) (hx : ringKrullDim (T.presheaf.stalk x) ≤ 1) :
    x ∈ V := by
  classical
  have key : ∀ y : T, y ⤳ x → t.base y = IsLocalRing.closedPoint R → y = x := by
    intro y hyx hys
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨𝔮, rfl⟩ : y ∈ Set.range (T.fromSpecStalk x).base := by
      rwa [Scheme.range_fromSpecStalk]
    let g : CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).presheaf.stalk (t.base x) :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ (t.base x) trivial
    let φ : CommRingCat.of R ⟶ T.presheaf.stalk x := g ≫ t.stalkMap x
    have hfac : T.fromSpecStalk x ≫ t = Spec.map φ := by
      rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk t, Spec.fromSpecStalk_eq]
    have hbase : t.base ((T.fromSpecStalk x).base 𝔮) = (Spec.map φ).base 𝔮 := by
      rw [← hfac]
      rfl
    have hcomap : ((Spec.map φ).base 𝔮).asIdeal = 𝔮.asIdeal.comap φ.hom := rfl
    have hϖ𝔮 : φ.hom ϖ ∈ 𝔮.asIdeal := by
      have h1 : ((Spec.map φ).base 𝔮).asIdeal = IsLocalRing.maximalIdeal R := by
        rw [← hbase, hys]
        rfl
      apply Ideal.mem_comap.mp
      rw [hcomap.symm, h1]
      apply (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
    have hgreg : IsSMulRegular ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) (g.hom ϖ) := by
      let _ : Algebra ((Spec (CommRingCat.of R)).presheaf.obj (op ⊤)) ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) :=
        ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (t.base x) trivial).hom.toAlgebra
      let _ := (isAffineOpen_top (Spec (CommRingCat.of R))).isLocalization_stalk ⟨t.base x, trivial⟩
      let _ : IsDomain ((Spec (CommRingCat.of R)).presheaf.obj (op ⊤)) :=
        Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
          (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
      have hle := ((isAffineOpen_top (Spec (CommRingCat.of R))).primeIdealOf
        ⟨t.base x, trivial⟩).asIdeal.primeCompl_le_nonZeroDivisors
      let _ : IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) :=
        IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
      have hne : g.hom ϖ ≠ 0 := by
        intro h0
        have hinj := IsLocalization.injective ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) hle
        have h0' : algebraMap ((Spec (CommRingCat.of R)).presheaf.obj (op ⊤)) ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ) = algebraMap ((Spec (CommRingCat.of R)).presheaf.obj (op ⊤)) ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) 0 := by
          rwa [map_zero]
        have := hinj h0'
        apply hϖ.ne_zero ((Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective (by rwa [map_zero]))
      refine (IsRegular.of_ne_zero hne).left.isSMulRegular
    let hflat : (t.stalkMap x).hom.Flat := Flat.stalkMap t x
    have hreg : IsSMulRegular (T.presheaf.stalk x) (φ.hom ϖ) := by
      let _ := (t.stalkMap x).hom.toAlgebra
      let _ : Module.Flat ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) (T.presheaf.stalk x) := hflat
      exact hgreg.of_flat
    have hnzd : φ.hom ϖ ∈ nonZeroDivisors (T.presheaf.stalk x) := by
      rw [mem_nonZeroDivisors_iff]
      refine ⟨fun a ha => hreg ?_, fun a ha => hreg ?_⟩
      ·
        change φ.hom ϖ * a = φ.hom ϖ * 0
        rwa [mul_zero]
      ·
        change φ.hom ϖ * a = φ.hom ϖ * 0
        rwa [mul_zero, mul_comm]
    have hnotmin : 𝔮.asIdeal ∉ minimalPrimes (T.presheaf.stalk x) := fun hmin =>
      Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hmin) hϖ𝔮 hnzd
    let _ : Ring.KrullDimLE 1 (T.presheaf.stalk x) := (Ring.krullDimLE_iff).mpr hx
    have hmax : 𝔮.asIdeal.IsMaximal :=
      ((Ring.krullDimLE_one_iff.mp inferInstance) 𝔮.asIdeal 𝔮.isPrime).resolve_left hnotmin
    have h𝔮 : 𝔮 = IsLocalRing.closedPoint (T.presheaf.stalk x) :=
      PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
    rw [h𝔮, Scheme.fromSpecStalk_closedPoint]
  have hS : IsClosed {y : T | t.base y = IsLocalRing.closedPoint R} := ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (IsLocalRing.maximalIdeal.isMaximal R)).preimage t.base.hom.continuous
  let _ : QuasiSober (Subtype (fun y : T => t.base y = IsLocalRing.closedPoint R)) :=
    hS.isClosedEmbedding_subtypeVal.quasiSober
  let xs : Subtype (fun y : T => t.base y = IsLocalRing.closedPoint R) := ⟨x, hxs⟩
  have hZ : closure ({xs} : Set (Subtype (fun y : T => t.base y = IsLocalRing.closedPoint R))) ∈ irreducibleComponents (Subtype (fun y : T => t.base y = IsLocalRing.closedPoint R)) := by
    refine ⟨isIrreducible_singleton.closure, fun W hW hZW => ?_⟩
    have hη := hW.isGenericPoint_genericPoint_closure
    have hxW : xs ∈ closure W := subset_closure (hZW (subset_closure (Set.mem_singleton xs)))
    have hηx : hW.genericPoint ⤳ xs := hη.specializes hxW
    have hηeq : hW.genericPoint = xs :=
      Subtype.ext (key hW.genericPoint.1 (hηx.map continuous_subtype_val) hW.genericPoint.2)
    have hcl : closure W = closure {xs} := by
      rw [← hηeq]
      apply hη.symm
    refine subset_closure.trans hcl.le
  obtain ⟨y, hyZ, hyV⟩ := hVs _ hZ
  apply ((specializes_iff_mem_closure.mpr hyZ).map continuous_subtype_val).mem_open V.isOpen hyV
/--
[AlgebraicGeometry_mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing.lean)
-/
@[path]
private lemma main
  (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {T : (Scheme : Type (u + 1))} (t : T ⟶ Spec (CommRingCat.of R)) [Flat t]
  (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
  (hVs : ∀ Z ∈ irreducibleComponents (Subtype (fun x : T => t.base x = IsLocalRing.closedPoint R)), ∃ x ∈ Z, x.1 ∈ V)
  (x : T) (hx : ringKrullDim (T.presheaf.stalk x) ≤ 1) :
    x ∈ V := by
  classical
  if hxs : t.base x = IsLocalRing.closedPoint R then
    apply mem_of_closedPoint R t V hVs x hxs hx
  else
    apply hVη x hxs


-- created on 2026-10-20
