import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorScheme
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite CartierDivisorScheme


namespace CartierDivisorScheme

/--
[structureUnitsSubgroup_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CartierDivisorScheme.lean)
-/
@[path]
lemma structureUnitsSubgroup_mono
  {X : Scheme.{u}}
  [IsIntegral X]
  {U V : X.Opens}
  [Nonempty U]
  [Nonempty V]
-- given
  (h : V ≤ U) :
-- imply
  structureUnitsSubgroup X U ≤ structureUnitsSubgroup X V := by
-- proof
  intro x hx
  simp only [structureUnitsSubgroup, MonoidHom.mem_range] at hx ⊢
  obtain ⟨φ, hφ⟩ := hx
  refine ⟨Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom φ, ?_⟩
  rw [← hφ]; ext
  simp only [structureUnitsToFunctionFieldUnits, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply]
  have key : X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField V =
    X.germToFunctionField U := by
    unfold Scheme.germToFunctionField
    rw [TopCat.Presheaf.germ_res]
  exact congrFun (congrArg DFunLike.coe (congrArg CommRingCat.Hom.hom key)) φ.val

end CartierDivisorScheme


-- created on 2026-10-23
