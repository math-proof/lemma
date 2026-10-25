import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInternalCylinderCoordinates
open StatMech StatMech.FrontierA


/--
[internalCylinderUpperCell_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderCoordinates.lean)
-/
@[path]
private lemma internalCylinderUpperCell_injective_eq
  {N m : Nat}
-- given
  (hNm : N <= m) :
-- imply
  Function.Injective (internalCylinderUpperCell N m hNm) := by
-- proof
  apply StatMech.FrontierA.internalCylinderUpperCell_injective N m hNm

/--
[internalCylinderBoundaryCell_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderCoordinates.lean)
-/
@[path]
private lemma internalCylinderBoundaryCell_injective_eq
  {N m : Nat}
-- given
  (hN : 0 < N)
  (hNm : N <= m) :
-- imply
  Function.Injective (internalCylinderBoundaryCell N m hN hNm) := by
-- proof
  apply StatMech.FrontierA.internalCylinderBoundaryCell_injective N m hN hNm

/--
[cubicalInternalCentralUpperVertices_eq_internalCylinderUpperCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderCoordinates.lean)
-/
@[path]
private lemma cubicalInternalCentralUpperVertices_eq_internalCylinderUpperCell_eq
  {N m : Nat}
-- given
  (hN : 0 < N)
  (hNm : N ≤ m) :
-- imply
  cubicalInternalCentralUpperVertices N m hNm = (Finset.univ : Finset (internalCylinderUpperIndex N)).image (fun ij => some (internalCylinderUpperCell N m hNm ij)) := by
-- proof
  apply StatMech.FrontierA.cubicalInternalCentralUpperVertices_eq_internalCylinderUpperCell N m hN hNm

/--
[oddCubicalCenteredSite_internalCylinderUpperCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderCoordinates.lean)
-/
@[path]
private lemma oddCubicalCenteredSite_internalCylinderUpperCell_eq
  {N m : Nat}
  {ij : internalCylinderUpperIndex N}
-- given
  (hNm : N <= m) :
-- imply
  oddCubicalCenteredSite m (internalCylinderUpperCell N m hNm ij) = internalCylinderUpperSite ij := by
-- proof
  apply StatMech.FrontierA.oddCubicalCenteredSite_internalCylinderUpperCell N m hNm ij

/--
[oddCubicalCenteredSite_internalCylinderBoundaryCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderCoordinates.lean)
-/
@[path]
private lemma oddCubicalCenteredSite_internalCylinderBoundaryCell_eq
  {N m : Nat}
  {q : CubicalCell N N N}
-- given
  (hN : 0 < N)
  (hNm : N <= m) :
-- imply
  oddCubicalCenteredSite m (internalCylinderBoundaryCell N m hN hNm q) = internalCylinderBoundarySite q := by
-- proof
  apply StatMech.FrontierA.oddCubicalCenteredSite_internalCylinderBoundaryCell N m hN hNm q

/--
[cubicalInternalCentralBoundaryVertices_eq_coordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderCoordinates.lean)
-/
@[path]
private lemma cubicalInternalCentralBoundaryVertices_eq_coordinate_eq
  {N m : Nat}
-- given
  (hN : 0 < N)
  (hNm : N ≤ m) :
-- imply
  cubicalInternalCentralBoundaryVertices N m = internalCylinderBoundaryCoordinateVertices N m hN hNm := by
-- proof
  apply StatMech.FrontierA.cubicalInternalCentralBoundaryVertices_eq_coordinate N m hN hNm


-- created on 2026-10-23
