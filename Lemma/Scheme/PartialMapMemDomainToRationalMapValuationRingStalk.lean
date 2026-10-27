import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {X Y S : (Scheme : Type (u + 1))}
private lemma fromSpecStalkOfMem_eq_of_specializes
  (U : X.Opens) {ξ x : X} (h : ξ ⤳ x)
  (hx : x ∈ U) (hξ : ξ ∈ U) :
  U.fromSpecStalkOfMem ξ hξ =
    Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem x hx := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
private lemma partialMap_fromSpecStalkOfMem_eq_of_specializes
  (f : X.PartialMap Y) {ξ x : X}
  (h : ξ ⤳ x) (hx : x ∈ f.domain) (hξ : ξ ∈ f.domain) :
  f.fromSpecStalkOfMem hξ =
    Spec.map (X.presheaf.stalkSpecializes h) ≫ f.fromSpecStalkOfMem hx := by
  change f.domain.fromSpecStalkOfMem ξ hξ ≫ f.hom =
    Spec.map (X.presheaf.stalkSpecializes h) ≫ f.domain.fromSpecStalkOfMem x hx ≫ f.hom
  rw [fromSpecStalkOfMem_eq_of_specializes f.domain h hx hξ, Category.assoc]
private lemma partialMap_fromFunctionField_eq_of_mem
  [IrreducibleSpace X] (f : X.PartialMap Y)
  {x : X} (hx : x ∈ f.domain) :
  f.fromFunctionField =
    Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫
      f.fromSpecStalkOfMem hx :=
  partialMap_fromSpecStalkOfMem_eq_of_specializes f (genericPoint_specializes x) hx
    ((genericPoint_specializes _).mem_open f.domain.2 f.dense_domain.nonempty.choose_spec)
private lemma ofHom_algebraMap_stalk_functionField
  [IrreducibleSpace X] (x : X) :
  CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
    X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
  simp_rw [RingHom.algebraMap_toAlgebra]
  apply CommRingCat.ofHom_hom _
private lemma existence_of_universallyClosed
  (f : Y ⟶ S) [hf : UniversallyClosed f] :
  ValuativeCriterion.Existence f := by
  apply ValuativeCriterion.Existence.of_specializingMap
  intro X' Y' i₁ i₂ f' hpb
  apply IsClosedMap.specializingMap (hf.universally_isClosedMap i₁ i₂ f' hpb)
/--
[AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.lean)
-/
@[path]
private lemma main
  {X Y S : (Scheme : Type (u + 1))} (sX : X ⟶ S) (sY : Y ⟶ S) [IsIntegral X]
  [LocallyOfFiniteType sY] (hY : ValuativeCriterion.Existence sY) (f : X.PartialMap Y)
  (hf : f.hom ≫ sY = f.domain.ι ≫ sX) (x : X) (hx : ValuationRing (X.presheaf.stalk x)) :
  x ∈ f.toRationalMap.domain := by
  let _ := hx
  have hcomm : f.fromFunctionField ≫ sY =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        (X.fromSpecStalk x ≫ sX) := by
    rw [ofHom_algebraMap_stalk_functionField]
    change (f.domain.fromSpecStalkOfMem (genericPoint X) _ ≫ f.hom) ≫ sY = _
    rw [Category.assoc, hf, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc]
  obtain ⟨l, hl₁, hl₂⟩ := (hY
    { R := X.presheaf.stalk x
      commRing := inferInstance
      domain := (inferInstance : IsDomain (X.presheaf.stalk x))
      valuationRing := hx
      K := X.functionField
      field := inferInstance
      algebra := (inferInstance : Algebra (X.presheaf.stalk x) X.functionField)
      isFractionRing := (inferInstance : IsFractionRing (X.presheaf.stalk x) X.functionField)
      i₁ := f.fromFunctionField
      i₂ := X.fromSpecStalk x ≫ sX
      commSq := ⟨hcomm⟩ }).exists_lift
  have hl₂' : l ≫ sY = X.fromSpecStalk x ≫ sX := hl₂
  have hl₁' : Spec.map (X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes trivial)) ≫ l = f.fromFunctionField := by
    rwa [← ofHom_algebraMap_stalk_functionField]
  refine Scheme.RationalMap.mem_domain.mpr
    ⟨Scheme.PartialMap.ofFromSpecStalk sX sY l hl₂',
     Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl₂', ?_⟩
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rwa [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq_of_mem _
      (Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl₂'),
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY l hl₂']


-- created on 2026-10-20
