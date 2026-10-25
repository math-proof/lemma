import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual.Part3
open Finset SimpleGraph StatMech StatMech.Onsager


/--
[kwg_pathEdgeIndices_map_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempDual.lean)
-/
@[path]
private lemma kwg_pathEdgeIndices_map_val_eq
  {P : PlanarZ2Subgraph}
  {u v : P.V}
  {path : P.G.Walk u v} :
-- imply
  (kwg_pathEdgeIndices P path).map Subtype.val = path.edges := by
-- proof
  apply StatMech.Onsager.kwg_pathEdgeIndices_map_val P path

/--
[kwg_pathDefectCount_cutSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempDual.lean)
-/
@[path]
private lemma kwg_pathDefectCount_cutSet_eq
  {P : PlanarZ2Subgraph}
  {config : ConfigSpace P.V}
  {u v : P.V}
  {path : P.G.Walk u v} :
-- imply
  kwg_pathDefectCount P path (kwg_cutSet (kwg_primalEnds P) config) = kwd_crossCount (kwd_sideBoundary config) path := by
-- proof
  apply StatMech.Onsager.kwg_pathDefectCount_cutSet P config path

/--
[kwg_pathDefectSign_cutSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempDual.lean)
-/
@[path]
private lemma kwg_pathDefectSign_cutSet_eq
  {P : PlanarZ2Subgraph}
  {config : ConfigSpace P.V}
  {u v : P.V}
  {path : P.G.Walk u v} :
-- imply
  kwg_pathDefectSign P path (kwg_cutSet (kwg_primalEnds P) config) = ons_lowTempPathSign P.G config path := by
-- proof
  apply StatMech.Onsager.kwg_pathDefectSign_cutSet P config path

/--
[ons_lowTempPathNumerator_eq_kwg_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempDual.lean)
-/
@[path]
private lemma ons_lowTempPathNumerator_eq_kwg_dual_eq
  {P : PlanarZ2Subgraph}
  {beta : Real}
  {u v : P.V}
  {path : P.G.Walk u v} :
-- imply
  ons_lowTempPathNumerator P.G beta path = (2 : Real) ^ Nat.card P.G.ConnectedComponent * kwg_lowTempPathDualSum P beta path := by
-- proof
  apply StatMech.Onsager.ons_lowTempPathNumerator_eq_kwg_dual P beta path

/--
[ons_lowTempContourDenominator_eq_kwg_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempDual.lean)
-/
@[path]
private lemma ons_lowTempContourDenominator_eq_kwg_dual_eq
  {P : PlanarZ2Subgraph}
  {beta : Real} :
-- imply
  ons_lowTempContourDenominator P.G beta = (2 : Real) ^ Nat.card P.G.ConnectedComponent * kwg_lowTempDualSum P beta := by
-- proof
  apply StatMech.Onsager.ons_lowTempContourDenominator_eq_kwg_dual P beta

/--
[isingExpectation_twoPoint_eq_kwg_lowTempDualRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempDual.lean)
-/
@[path]
private lemma isingExpectation_twoPoint_eq_kwg_lowTempDualRatio_eq
  {P : PlanarZ2Subgraph}
  {beta : Real}
  {u v : P.V}
  {path : P.G.Walk u v} :
-- imply
  isingExpectation P.G beta 0 (fun config => spin config u * spin config v) = kwg_lowTempPathDualSum P beta path / kwg_lowTempDualSum P beta := by
-- proof
  apply StatMech.Onsager.isingExpectation_twoPoint_eq_kwg_lowTempDualRatio P beta path


-- created on 2026-10-23
