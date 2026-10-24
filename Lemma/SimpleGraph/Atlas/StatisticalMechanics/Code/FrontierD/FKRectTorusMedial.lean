import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial
open StatMech StatMech.FrontierD


/--
[fkRectConfigurationToMedialPairing_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusMedial.lean)
-/
@[path]
private lemma fkRectConfigurationToMedialPairing_apply_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {v : R.medialTorus.Vertex} :
-- imply
  fkRectConfigurationToMedialPairing R omega v = (omega (fkRectTorusMedialEdgeEquiv R v) ^^ fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R v)) := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationToMedialPairing_apply R omega v

/--
[finitePeriodicSucc_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusMedial.lean)
-/
@[path]
private lemma finitePeriodicSucc_ne_self_eq
  {N : Nat}
  {i : Fin N}
-- given
  (hN : 1 < N) :
-- imply
  finitePeriodicSucc (lt_trans Nat.zero_lt_one hN) i ≠ i := by
-- proof
  apply StatMech.FrontierD.finitePeriodicSucc_ne_self hN i

/--
[cyclicPred_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusMedial.lean)
-/
@[path]
private lemma cyclicPred_ne_self_eq
  {N : Nat}
  {i : Fin N}
-- given
  (hN : 1 < N) :
-- imply
  SixVertexArrows.cyclicPred (lt_trans Nat.zero_lt_one hN) i ≠ i := by
-- proof
  apply StatMech.FrontierD.cyclicPred_ne_self hN i

/--
[fkRectTorusIndexedEdge_ne_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusMedial.lean)
-/
@[path]
private lemma fkRectTorusIndexedEdge_ne_diag_eq
  {R : FKRectTorus}
  {a : R.EdgeIndex}
  {x : R.Vertex} :
-- imply
  fkRectTorusIndexedEdge R a ≠ s(x, x) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusIndexedEdge_ne_diag R a x


-- created on 2026-10-23
