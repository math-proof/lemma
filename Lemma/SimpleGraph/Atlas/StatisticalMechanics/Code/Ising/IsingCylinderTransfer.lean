import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.IsingCylinderTransfer
open Finset Matrix Filter Topology StatMech StatMech.Ising


/--
[cylinderInterLayerInteraction_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean)
-/
@[path]
private lemma cylinderInterLayerInteraction_symm_eq
  [Fintype W]
  [DecidableEq W]
  [Nonempty W]
  {s t : ConfigSpace W}
-- given
  (Jvertical : W -> Real) :
-- imply
  cylinderInterLayerInteraction Jvertical s t = cylinderInterLayerInteraction Jvertical t s := by
-- proof
  apply StatMech.Ising.cylinderInterLayerInteraction_symm Jvertical s t

/--
[isingCylinderTransfer_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean)
-/
@[path]
private lemma isingCylinderTransfer_isHermitian_eq
  [Fintype W]
  [DecidableEq W]
  [Nonempty W]
  {E : Finset (Sym2 W)}
-- given
  (J : Sym2 W -> Real)
  (h Jvertical : W -> Real) :
-- imply
  (isingCylinderTransfer E J h Jvertical).IsHermitian := by
-- proof
  apply StatMech.Ising.isingCylinderTransfer_isHermitian E J h Jvertical

/--
[isingCylinderTransfer_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean)
-/
@[path]
private lemma isingCylinderTransfer_pos_eq
  [Fintype W]
  [DecidableEq W]
  [Nonempty W]
  {E : Finset (Sym2 W)}
  {s t : ConfigSpace W}
-- given
  (J : Sym2 W -> Real)
  (h Jvertical : W -> Real) :
-- imply
  0 < isingCylinderTransfer E J h Jvertical s t := by
-- proof
  apply StatMech.Ising.isingCylinderTransfer_pos E J h Jvertical s t

/--
[isingCylinderBoundaryVector_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean)
-/
@[path]
private lemma isingCylinderBoundaryVector_pos_eq
  [Fintype W]
  [DecidableEq W]
  [Nonempty W]
  {E : Finset (Sym2 W)}
  {s : ConfigSpace W}
-- given
  (J : Sym2 W -> Real)
  (h : W -> Real)
  (boundary : ConfigSpace W -> Real) :
-- imply
  0 < isingCylinderBoundaryVector E J h boundary s := by
-- proof
  apply StatMech.Ising.isingCylinderBoundaryVector_pos E J h boundary s

/--
[isingCylinderEndpointMean_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean)
-/
@[path]
private lemma isingCylinderEndpointMean_tendsto_eq
  [Fintype W]
  [DecidableEq W]
  [Nonempty W]
  {E : Finset (Sym2 W)}
-- given
  (J : Sym2 W -> Real)
  (h Jvertical : W -> Real)
  (leftBoundary rightBoundary : ConfigSpace W -> Real)
  (obs : ConfigSpace W -> Real) :
-- imply
  exists lam : Real, 0 < lam ∧ exists u : EuclideanSpace Real (ConfigSpace W), (forall s, 0 < u s) ∧ norm u = 1 ∧ isingCylinderTransfer E J h Jvertical *ᵥ (fun s => u s) = lam • (fun s => u s) ∧ Tendsto (isingCylinderEndpointMean E J h Jvertical leftBoundary rightBoundary obs) atTop (nhds ((∑ s, isingCylinderBoundaryVector E J h rightBoundary s * obs s * u s) / ∑ s, isingCylinderBoundaryVector E J h rightBoundary s * u s)) := by
-- proof
  apply StatMech.Ising.isingCylinderEndpointMean_tendsto E J h Jvertical leftBoundary rightBoundary obs

/--
[isingCylinderEndpointSpin_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean)
-/
@[path]
private lemma isingCylinderEndpointSpin_tendsto_eq
  [Fintype W]
  [DecidableEq W]
  [Nonempty W]
  {E : Finset (Sym2 W)}
  {x : W}
-- given
  (J : Sym2 W -> Real)
  (h Jvertical : W -> Real)
  (leftBoundary rightBoundary : ConfigSpace W -> Real) :
-- imply
  exists m : Real, Tendsto (isingCylinderEndpointMean E J h Jvertical leftBoundary rightBoundary (fun s => spin s x)) atTop (nhds m) := by
-- proof
  apply StatMech.Ising.isingCylinderEndpointSpin_tendsto E J h Jvertical leftBoundary rightBoundary x

/--
[isingCylinder_twoBoundaryEndpoint_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean)
-/
@[path]
private lemma isingCylinder_twoBoundaryEndpoint_common_eq
  [Fintype W]
  [DecidableEq W]
  [Nonempty W]
  {E : Finset (Sym2 W)}
-- given
  (J : Sym2 W -> Real)
  (h Jvertical : W -> Real)
  (leftBoundaryA leftBoundaryB rightBoundary : ConfigSpace W -> Real)
  (obs : ConfigSpace W -> Real) :
-- imply
  exists m : Real, Tendsto (isingCylinderEndpointMean E J h Jvertical leftBoundaryA rightBoundary obs) atTop (nhds m) ∧ Tendsto (isingCylinderEndpointMean E J h Jvertical leftBoundaryB rightBoundary obs) atTop (nhds m) := by
-- proof
  apply StatMech.Ising.isingCylinder_twoBoundaryEndpoint_common E J h Jvertical leftBoundaryA leftBoundaryB rightBoundary obs

/--
[isingCylinder_twoBoundarySpin_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean)
-/
@[path]
private lemma isingCylinder_twoBoundarySpin_common_eq
  [Fintype W]
  [DecidableEq W]
  [Nonempty W]
  {E : Finset (Sym2 W)}
  {x : W}
-- given
  (J : Sym2 W -> Real)
  (h Jvertical : W -> Real)
  (leftBoundaryA leftBoundaryB rightBoundary : ConfigSpace W -> Real) :
-- imply
  exists m : Real, Tendsto (isingCylinderEndpointMean E J h Jvertical leftBoundaryA rightBoundary (fun s => spin s x)) atTop (nhds m) ∧ Tendsto (isingCylinderEndpointMean E J h Jvertical leftBoundaryB rightBoundary (fun s => spin s x)) atTop (nhds m) := by
-- proof
  apply StatMech.Ising.isingCylinder_twoBoundarySpin_common E J h Jvertical leftBoundaryA leftBoundaryB rightBoundary x

/--
[isingCylinderPartition_log_div_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean)
-/
@[path]
private lemma isingCylinderPartition_log_div_tendsto_eq
  [Fintype W]
  [DecidableEq W]
  [Nonempty W]
  {E : Finset (Sym2 W)}
-- given
  (J : Sym2 W -> Real)
  (h Jvertical : W -> Real)
  (leftBoundary rightBoundary : ConfigSpace W -> Real) :
-- imply
  exists lam : Real, 0 < lam ∧ Tendsto (fun n : Nat => Real.log (isingCylinderPartition E J h Jvertical leftBoundary rightBoundary n) / (n : Real)) atTop (nhds (Real.log lam)) := by
-- proof
  apply StatMech.Ising.isingCylinderPartition_log_div_tendsto E J h Jvertical leftBoundary rightBoundary


-- created on 2026-10-23
