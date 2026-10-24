import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality
open StatMech StatMech.FrontierA StatMech.FrontierA.CellularRibbonDualData


/--
[eulerBaseParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialCellularRibbonDuality.lean)
-/
@[path]
private lemma eulerBaseParity_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R} :
-- imply
  (Fintype.card E + permCycleCount R.rotation) % 2 = C.dualVertexCount % 2 := by
-- proof
  apply StatMech.FrontierA.CellularRibbonDualData.eulerBaseParity C

/--
[boundaryParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialCellularRibbonDuality.lean)
-/
@[path]
private lemma boundaryParity_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R} :
-- imply
  forall F : Finset E, (Fᶜ.card + R.boundaryComponents F) % 2 = C.dualVertexCount % 2 := by
-- proof
  apply StatMech.FrontierA.CellularRibbonDualData.boundaryParity C

/--
[dualRibbonBoundaryCharacterCoefficient_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialCellularRibbonDuality.lean)
-/
@[path]
private lemma dualRibbonBoundaryCharacterCoefficient_compl_eq
  [Fintype D]
  [DecidableEq D]
  [Field K]
  {R : RibbonPermutationSystem E D}
  {F : Finset E}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> K)
  (hcharacter : forall (F : Finset E) (b : Fin (R.boundaryComponents F)), character F b ≠ 0)
  (htotal : forall F : Finset E, ∏ b, character F b = 1) :
-- imply
  dualRibbonBoundaryCharacterCoefficient R character Fᶜ = (-1 : K) ^ R.boundaryComponents F * ribbonBoundaryCharacterCoefficient R character F := by
-- proof
  apply StatMech.FrontierA.dualRibbonBoundaryCharacterCoefficient_compl R character hcharacter htotal F

/--
[cellularRibbon_kwDualSubgraphSum_complement_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialCellularRibbonDuality.lean)
-/
@[path]
private lemma cellularRibbon_kwDualSubgraphSum_complement_duality_eq
  [Fintype D]
  [DecidableEq D]
  [Field K]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> K)
  (hcharacter : forall (F : Finset E) (b : Fin (R.boundaryComponents F)), character F b ≠ 0)
  (htotal : forall F : Finset E, ∏ b, character F b = 1)
  (weight : E -> K)
  (hweight : forall e, weight e ≠ 0) :
-- imply
  kwDualSubgraphSum (dualRibbonBoundaryCharacterCoefficient R character) (fun e => -(weight e)⁻¹) = (-1 : K) ^ C.dualVertexCount * ((∏ e : E, weight e)⁻¹ * kwDualSubgraphSum (ribbonBoundaryCharacterCoefficient R character) weight) := by
-- proof
  apply StatMech.FrontierA.cellularRibbon_kwDualSubgraphSum_complement_duality R C character hcharacter htotal weight hweight

/--
[cellularRibbon_isoradialCritical_subgraphSum_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialCellularRibbonDuality.lean)
-/
@[path]
private lemma cellularRibbon_isoradialCritical_subgraphSum_duality_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex)
  (hcharacter : forall (F : Finset E) (b : Fin (R.boundaryComponents F)), character F b ≠ 0)
  (htotal : forall F : Finset E, ∏ b, character F b = 1)
  (theta : E -> Real)
  (htheta : forall e, 0 < theta e)
  (htheta' : forall e, theta e < Real.pi / 2) :
-- imply
  kwDualSubgraphSum (dualRibbonBoundaryCharacterCoefficient R character) (fun e => isoradialCriticalMu (Real.pi / 2 - theta e)) = (-1 : Complex) ^ C.dualVertexCount * ((∏ e : E, isoradialCriticalMu (theta e))⁻¹ * kwDualSubgraphSum (ribbonBoundaryCharacterCoefficient R character) (fun e => isoradialCriticalMu (theta e))) := by
-- proof
  apply StatMech.FrontierA.cellularRibbon_isoradialCritical_subgraphSum_duality R C character hcharacter htotal theta htheta htheta'


-- created on 2026-10-23
