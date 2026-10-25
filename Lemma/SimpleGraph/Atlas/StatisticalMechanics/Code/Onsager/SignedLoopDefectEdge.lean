import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopDefectEdge.Part2
open Finset SimpleGraph StatMech StatMech.Onsager


/--
[insert_defect_hasOddBoundary_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdge.lean)
-/
@[path]
private lemma insert_defect_hasOddBoundary_iff_eq
  [Fintype V]
  [DecidableEq V]
  {u v : V}
  {F : Finset (Sym2 V)}
-- given
  (huv : u ≠ v)
  (heF : s(u, v) ∉ F) :
-- imply
  HasOddBoundary (insert s(u, v) F) ∅ ↔ HasOddBoundary F {u, v} := by
-- proof
  apply StatMech.Onsager.insert_defect_hasOddBoundary_iff huv heF

/--
[ons_defectEdgeX_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdge.lean)
-/
@[path]
private lemma ons_defectEdgeX_eq_eq
  [Fintype V]
  [DecidableEq V]
  {u v : V}
  {x z : Real}
-- given
  (huv : u ≠ v)
  (hnotAdj : ¬ G.Adj u v) :
-- imply
  ons_defectEdgeX G u v x z = ons_X G x + z * ons_sourceX G {u, v} x := by
-- proof
  apply StatMech.Onsager.ons_defectEdgeX_eq huv hnotAdj x z

/--
[hasDerivAt_ons_defectEdgeX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdge.lean)
-/
@[path]
private lemma hasDerivAt_ons_defectEdgeX_eq
  [Fintype V]
  [DecidableEq V]
  {u v : V}
  {x z : Real}
-- given
  (huv : u ≠ v)
  (hnotAdj : ¬ G.Adj u v) :
-- imply
  HasDerivAt (ons_defectEdgeX G u v x) (ons_sourceX G {u, v} x) z := by
-- proof
  apply StatMech.Onsager.hasDerivAt_ons_defectEdgeX huv hnotAdj x z

/--
[ons_sourceX_eq_disorderX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdge.lean)
-/
@[path]
private lemma ons_sourceX_eq_disorderX_eq
  [Fintype V]
  [DecidableEq V]
  {u v : V}
  {Q : Finset (Sym2 V)}
  {x : Real}
-- given
  (hQsub : Q ⊆ G.edgeFinset)
  (hQ : HasOddBoundary Q {u, v}) :
-- imply
  ons_sourceX G {u, v} x = ons_disorderX G Q x := by
-- proof
  apply StatMech.Onsager.ons_sourceX_eq_disorderX hQsub hQ x


-- created on 2026-10-23
