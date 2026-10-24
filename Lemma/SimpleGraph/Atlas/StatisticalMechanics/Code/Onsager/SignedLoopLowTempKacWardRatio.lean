import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SignedLoopLowTempKacWardRatio
open StatMech StatMech.Onsager


/--
[kwg_lowTempDualSum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWardRatio.lean)
-/
@[path]
private lemma kwg_lowTempDualSum_pos_eq
  {P : PlanarZ2Subgraph}
  {beta : Real} :
-- imply
  0 < kwg_lowTempDualSum P beta := by
-- proof
  apply StatMech.Onsager.kwg_lowTempDualSum_pos P beta

/--
[coe_isingExpectation_twoPoint_sq_eq_lowTempKacWard_detRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWardRatio.lean)
-/
@[path]
private lemma coe_isingExpectation_twoPoint_sq_eq_lowTempKacWard_detRatio_eq
  {P : PlanarZ2Subgraph}
  {beta : Real}
  {u v : P.V}
  {path : P.G.Walk u v}
  {embedding : KWStraightLineEmbedding (kwg_subdivGraph (kwg_dualEnds P))} :
-- imply
  (isingExpectation P.G beta 0 (fun config => spin config u * spin config v) : Complex) ^ 2 = (1 - kwGraphTransition (kwg_subdivGraph (kwg_dualEnds P)) (kwg_subdivWeight (V := kwg_Face P) (fun e => kwg_pathEdgeSign P path e * (Real.exp (-2 * beta) : Complex))) embedding.turnPhase).det / (1 - kwGraphTransition (kwg_subdivGraph (kwg_dualEnds P)) (kwg_subdivWeight (V := kwg_Face P) (fun _ => (Real.exp (-2 * beta) : Complex))) embedding.turnPhase).det := by
-- proof
  apply StatMech.Onsager.coe_isingExpectation_twoPoint_sq_eq_lowTempKacWard_detRatio P beta path embedding


-- created on 2026-10-23
