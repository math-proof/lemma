import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[AlgebraicGeometry_Flat_isDomain_stalk_of_isDomain_stalk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Flat_isDomain_stalk_of_isDomain_stalk.lean)
-/
@[path]
private lemma main
  {Y Z : Scheme} {y : Y} {h : Y ⟶ Z} [Flat h]
-- given
  [IsDomain (Y.presheaf.stalk y)] :
-- imply
  IsDomain (Z.presheaf.stalk (h y)) := by
-- proof
  have hflat : (h.stalkMap y).hom.Flat := Flat.stalkMap h y
  let _ := (h.stalkMap y).hom.toAlgebra
  let _ : Module.Flat (Z.presheaf.stalk (h y)) (Y.presheaf.stalk y) := hflat
  let _ : IsLocalHom (algebraMap (Z.presheaf.stalk (h y)) (Y.presheaf.stalk y)) := by
    rw [RingHom.algebraMap_toAlgebra]; infer_instance
  let _ : Module.FaithfullyFlat (Z.presheaf.stalk (h y)) (Y.presheaf.stalk y) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (algebraMap (Z.presheaf.stalk (h y)) (Y.presheaf.stalk y)) :=
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance).injective
  refine hinj.isDomain


-- created on 2026-10-20
