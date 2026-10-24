import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismGeometry
open StatMech StatMech.FrontierA


/--
[finOddEquivCenteredInt_apply_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismGeometry.lean)
-/
@[path]
private lemma finOddEquivCenteredInt_apply_val_eq
  {n : Nat}
  {i : Fin (2 * n + 1)} :
-- imply
  (finOddEquivCenteredInt n i).1 = (i.val : Int) - n := by
-- proof
  apply StatMech.FrontierA.finOddEquivCenteredInt_apply_val n i

/--
[rectangularPrismSiteEquivSctBoxDobrushin_apply_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismGeometry.lean)
-/
@[path]
private lemma rectangularPrismSiteEquivSctBoxDobrushin_apply_zero_eq
  {n : Nat}
  {v : StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n} :
-- imply
  (rectangularPrismSiteEquivSctBoxDobrushin n v).1 0 = (v.x.val : Int) - n := by
-- proof
  apply StatMech.FrontierA.rectangularPrismSiteEquivSctBoxDobrushin_apply_zero n v

/--
[rectangularPrismSiteEquivSctBoxDobrushin_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismGeometry.lean)
-/
@[path]
private lemma rectangularPrismSiteEquivSctBoxDobrushin_apply_one_eq
  {n : Nat}
  {v : StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n} :
-- imply
  (rectangularPrismSiteEquivSctBoxDobrushin n v).1 1 = (v.y.val : Int) - n := by
-- proof
  apply StatMech.FrontierA.rectangularPrismSiteEquivSctBoxDobrushin_apply_one n v

/--
[rectangularPrismSiteEquivSctBoxDobrushin_apply_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismGeometry.lean)
-/
@[path]
private lemma rectangularPrismSiteEquivSctBoxDobrushin_apply_two_eq
  {n : Nat}
  {v : StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n} :
-- imply
  (rectangularPrismSiteEquivSctBoxDobrushin n v).1 2 = (n : Int) - v.z.val := by
-- proof
  apply StatMech.FrontierA.rectangularPrismSiteEquivSctBoxDobrushin_apply_two n v

/--
[interfaceField_rectangularPrismSiteEquivSctBoxDobrushin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismGeometry.lean)
-/
@[path]
private lemma interfaceField_rectangularPrismSiteEquivSctBoxDobrushin_eq
  {n : Nat}
  {v : StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n} :
-- imply
  StatMech.Ising.interfaceField (⟨2, by omega⟩ : Fin 3) (rectangularPrismSiteEquivSctBoxDobrushin n v).1 = decide (v.z.val <= n) := by
-- proof
  apply StatMech.FrontierA.interfaceField_rectangularPrismSiteEquivSctBoxDobrushin n v

/--
[rectangularPrismConfigEquivSctBoxDobrushin_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismGeometry.lean)
-/
@[path]
private lemma rectangularPrismConfigEquivSctBoxDobrushin_apply_eq
  {n : Nat}
  {sigma : StatMech.Ising.RectangularPrismConfig (2 * n + 1) (2 * n + 1) n}
  {v : StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n} :
-- imply
  rectangularPrismConfigEquivSctBoxDobrushin n sigma (rectangularPrismSiteEquivSctBoxDobrushin n v) = sigma v := by
-- proof
  apply StatMech.FrontierA.rectangularPrismConfigEquivSctBoxDobrushin_apply n sigma v


-- created on 2026-10-23
