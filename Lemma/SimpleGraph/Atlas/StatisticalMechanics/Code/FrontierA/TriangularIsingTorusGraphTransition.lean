import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition.Part6
open StatMech StatMech.FrontierA


/--
[triangularTorusDartEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean)
-/
@[path]
private lemma triangularTorusDartEquiv_apply_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : triangularTorusDart L} :
-- imply
  triangularTorusDartEquiv L d = triangularTorusDartToGraphDart L d := by
-- proof
  apply StatMech.FrontierA.triangularTorusDartEquiv_apply L d

/--
[triangularTorusEdgeWeight_dart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean)
-/
@[path]
private lemma triangularTorusEdgeWeight_dart_eq
  {L : Nat}
  [Fact (2 < L)]
  {t1 t2 t3 : Complex}
  {d : triangularTorusDart L} :
-- imply
  triangularTorusEdgeWeight L t1 t2 t3 (triangularTorusDartEquiv L d).edge = triangularTorusDirectionWeight t1 t2 t3 d.2 := by
-- proof
  apply StatMech.FrontierA.triangularTorusEdgeWeight_dart L t1 t2 t3 d

/--
[triangularTorusDirectionStep_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean)
-/
@[path]
private lemma triangularTorusDirectionStep_reverse_eq
  {L : Nat}
  {a : Fin 6} :
-- imply
  triangularTorusDirectionStep L (triangularTorusDirectionReverse a) = -triangularTorusDirectionStep L a := by
-- proof
  apply StatMech.FrontierA.triangularTorusDirectionStep_reverse L a

/--
[triangularTorusDartEquiv_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean)
-/
@[path]
private lemma triangularTorusDartEquiv_reverse_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : triangularTorusDart L} :
-- imply
  triangularTorusDartEquiv L (triangularTorusDartReverse L d) = (triangularTorusDartEquiv L d).symm := by
-- proof
  apply StatMech.FrontierA.triangularTorusDartEquiv_reverse L d

/--
[triangularKacWardTurnMatrix_reverse_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean)
-/
@[path]
private lemma triangularKacWardTurnMatrix_reverse_zero_eq
  {rho : Complex}
  {a : Fin 6} :
-- imply
  triangularKacWardTurnMatrix rho a (triangularTorusDirectionReverse a) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularKacWardTurnMatrix_reverse_zero rho a

/--
[kwGraphTransition_triangularTorusDartEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean)
-/
@[path]
private lemma kwGraphTransition_triangularTorusDartEquiv_apply_eq
  {L : Nat}
  [Fact (2 < L)]
  {t1 t2 t3 rho u v : Complex}
  {d e : triangularTorusDart L} :
-- imply
  kwGraphTransition (triangularTorusGraph L) (triangularTorusEdgeWeight L t1 t2 t3) (triangularTorusGraphPhase L rho u v) (triangularTorusDartEquiv L d) (triangularTorusDartEquiv L e) = if (triangularTorusDartEquiv L d).snd = (triangularTorusDartEquiv L e).fst ∧ (triangularTorusDartEquiv L d).edge ≠ (triangularTorusDartEquiv L e).edge then triangularTorusDirectionWeight t1 t2 t3 d.2 * (triangularTorusDirectionPhase u v d.2 * triangularKacWardTurnMatrix rho d.2 e.2) else 0 := by
-- proof
  apply StatMech.FrontierA.kwGraphTransition_triangularTorusDartEquiv_apply L t1 t2 t3 rho u v d e

/--
[triangularTorusDartEquiv_consecutive_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean)
-/
@[path]
private lemma triangularTorusDartEquiv_consecutive_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {d e : triangularTorusDart L} :
-- imply
  (triangularTorusDartEquiv L d).snd = (triangularTorusDartEquiv L e).fst ↔ (d.1.1 - e.1.1, d.1.2 - e.1.2) = triangularTorusDirectionStep L d.2 := by
-- proof
  apply StatMech.FrontierA.triangularTorusDartEquiv_consecutive_iff L d e

/--
[triangularTorusDartEquiv_edge_eq_iff_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean)
-/
@[path]
private lemma triangularTorusDartEquiv_edge_eq_iff_reverse_eq
  {L : Nat}
  [Fact (2 < L)]
  {d e : triangularTorusDart L}
-- given
  (hc : (triangularTorusDartEquiv L d).snd = (triangularTorusDartEquiv L e).fst) :
-- imply
  (triangularTorusDartEquiv L d).edge = (triangularTorusDartEquiv L e).edge ↔ e = triangularTorusDartReverse L d := by
-- proof
  apply StatMech.FrontierA.triangularTorusDartEquiv_edge_eq_iff_reverse L d e hc

/--
[triangularTorusKWMatrix_eq_reindex_graphTransition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean)
-/
@[path]
private lemma triangularTorusKWMatrix_eq_reindex_graphTransition_eq
  {L : Nat}
  [Fact (2 < L)]
  {t1 t2 t3 rho u v : Complex} :
-- imply
  triangularTorusKWMatrix L t1 t2 t3 rho u v = (Matrix.reindex (triangularTorusDartEquiv L).symm (triangularTorusDartEquiv L).symm) (kwGraphTransition (triangularTorusGraph L) (triangularTorusEdgeWeight L t1 t2 t3) (triangularTorusGraphPhase L rho u v)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusKWMatrix_eq_reindex_graphTransition L t1 t2 t3 rho u v

/--
[det_one_sub_triangularTorusKWMatrix_eq_graphTransition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean)
-/
@[path]
private lemma det_one_sub_triangularTorusKWMatrix_eq_graphTransition_eq
  {L : Nat}
  [Fact (2 < L)]
  {t1 t2 t3 rho u v : Complex} :
-- imply
  (1 - triangularTorusKWMatrix L t1 t2 t3 rho u v).det = (1 - kwGraphTransition (triangularTorusGraph L) (triangularTorusEdgeWeight L t1 t2 t3) (triangularTorusGraphPhase L rho u v)).det := by
-- proof
  apply StatMech.FrontierA.det_one_sub_triangularTorusKWMatrix_eq_graphTransition L t1 t2 t3 rho u v


-- created on 2026-10-23
