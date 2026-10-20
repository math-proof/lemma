import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma final_opensMap
  {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y) :
  (TopologicalSpace.Opens.map f.base).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun U => ⟨⊤, ⟨homOfLE le_top⟩⟩)
    (fun {U} {V} s s' => ⟨V, 𝟙 V, by rw [Subsingleton.elim s s']⟩)
private lemma helper_main
  {X Y : (Scheme : Type (u + 1))} (g : X ⟶ Y) :
  Nonempty ((Scheme.Modules.pullback g).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf) := by
  let _ := final_opensMap g
  have hiso : IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) := inferInstance
  refine ⟨@asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) hiso⟩
/--
[AlgebraicGeometry_Scheme_Modules_nonempty_pullback_obj_unit_iso_unit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_obj_unit_iso_unit.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))} (g : X ⟶ Y) :
  -- imply
  Nonempty ((Scheme.Modules.pullback g).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf) := by
  -- proof
  apply helper_main g


-- created on 2026-10-20
