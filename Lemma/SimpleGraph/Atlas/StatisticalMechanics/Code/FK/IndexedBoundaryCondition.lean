import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.IndexedBoundaryCondition
open SimpleGraph StatMech StatMech.FK


/--
[indexedOpenGraph_inf_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean)
-/
@[path]
private lemma indexedOpenGraph_inf_le_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (ends : E -> Sym2 V)
  (a b : E -> Bool) :
-- imply
  indexedOpenGraph ends (a ⊓ b) <= indexedOpenGraph ends a ⊓ indexedOpenGraph ends b := by
-- proof
  apply StatMech.FK.indexedOpenGraph_inf_le ends a b

/--
[indexedOpenGraph_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean)
-/
@[path]
private lemma indexedOpenGraph_sup_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (ends : E -> Sym2 V)
  (a b : E -> Bool) :
-- imply
  indexedOpenGraph ends (a ⊔ b) = indexedOpenGraph ends a ⊔ indexedOpenGraph ends b := by
-- proof
  apply StatMech.FK.indexedOpenGraph_sup ends a b

/--
[indexedEdgeProduct_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean)
-/
@[path]
private lemma indexedEdgeProduct_pos_eq
  [Fintype V]
  [DecidableEq V]
  {p : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (omega : E -> Bool) :
-- imply
  0 < indexedEdgeProduct p omega := by
-- proof
  apply StatMech.FK.indexedEdgeProduct_pos hp hp1 omega

/--
[indexedEdgeProduct_logModular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean)
-/
@[path]
private lemma indexedEdgeProduct_logModular_eq
  [Fintype V]
  [DecidableEq V]
  {p : Real}
-- given
  (a b : E -> Bool) :
-- imply
  indexedEdgeProduct p a * indexedEdgeProduct p b = indexedEdgeProduct p (a ⊓ b) * indexedEdgeProduct p (a ⊔ b) := by
-- proof
  apply StatMech.FK.indexedEdgeProduct_logModular p a b

/--
[card_connectedComponent_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean)
-/
@[path]
private lemma card_connectedComponent_antitone_eq
  [Fintype V]
  [DecidableEq V]
  {G H : SimpleGraph V}
-- given
  (hGH : G <= H) :
-- imply
  Nat.card H.ConnectedComponent <= Nat.card G.ConnectedComponent := by
-- proof
  apply StatMech.FK.card_connectedComponent_antitone hGH

/--
[indexedMixed_supermodular_bc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean)
-/
@[path]
private lemma indexedMixed_supermodular_bc_eq
  [Fintype V]
  [DecidableEq V]
  {C C' : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidableRel C'.Adj]
-- given
  (ends : E -> Sym2 V)
  (hCC' : C <= C')
  (a b : E -> Bool) :
-- imply
  indexedNumClustersBC ends C a + indexedNumClustersBC ends C' b <= indexedNumClustersBC ends C (a ⊓ b) + indexedNumClustersBC ends C' (a ⊔ b) := by
-- proof
  apply StatMech.FK.indexedMixed_supermodular_bc ends C C' hCC' a b

/--
[indexedBcWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean)
-/
@[path]
private lemma indexedBcWeight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : Real}
-- given
  (ends : E -> Sym2 V)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (omega : E -> Bool) :
-- imply
  0 < indexedBcWeight ends C p q omega := by
-- proof
  apply StatMech.FK.indexedBcWeight_pos ends C hp hp1 hq omega

/--
[indexedBcZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean)
-/
@[path]
private lemma indexedBcZ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : Real}
-- given
  (ends : E -> Sym2 V)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < indexedBcZ ends C p q := by
-- proof
  apply StatMech.FK.indexedBcZ_pos ends C hp hp1 hq

/--
[indexedBcProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean)
-/
@[path]
private lemma indexedBcProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : Real}
-- given
  (ends : E -> Sym2 V)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (omega : E -> Bool) :
-- imply
  0 <= indexedBcProb ends C p q omega := by
-- proof
  apply StatMech.FK.indexedBcProb_nonneg ends C hp hp1 hq omega

/--
[indexedBcProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean)
-/
@[path]
private lemma indexedBcProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : Real}
-- given
  (ends : E -> Sym2 V)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ omega : E -> Bool, indexedBcProb ends C p q omega = 1 := by
-- proof
  apply StatMech.FK.indexedBcProb_sum_eq_one ends C hp hp1 hq

/--
[indexedBcWeight_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean)
-/
@[path]
private lemma indexedBcWeight_cross_eq
  [Fintype V]
  [DecidableEq V]
  {C C' : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidableRel C'.Adj]
  {p q : Real}
-- given
  (ends : E -> Sym2 V)
  (hCC' : C <= C')
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (a b : E -> Bool) :
-- imply
  indexedBcWeight ends C p q a * indexedBcWeight ends C' p q b <= indexedBcWeight ends C p q (a ⊓ b) * indexedBcWeight ends C' p q (a ⊔ b) := by
-- proof
  apply StatMech.FK.indexedBcWeight_cross ends C C' hCC' hp hp1 hq a b

/--
[indexedBcProb_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean)
-/
@[path]
private lemma indexedBcProb_cross_eq
  [Fintype V]
  [DecidableEq V]
  {C C' : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidableRel C'.Adj]
  {p q : Real}
-- given
  (ends : E -> Sym2 V)
  (hCC' : C <= C')
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (a b : E -> Bool) :
-- imply
  indexedBcProb ends C p q a * indexedBcProb ends C' p q b <= indexedBcProb ends C p q (a ⊓ b) * indexedBcProb ends C' p q (a ⊔ b) := by
-- proof
  apply StatMech.FK.indexedBcProb_cross ends C C' hCC' hp hp1 hq a b

/--
[indexedBcEventMass_mono_bc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean)
-/
@[path]
private lemma indexedBcEventMass_mono_bc_eq
  [Fintype V]
  [DecidableEq V]
  {C C' : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidableRel C'.Adj]
  {p q : Real}
  {A : Set (E -> Bool)}
-- given
  (ends : E -> Sym2 V)
  (hCC' : C <= C')
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A) :
-- imply
  indexedBcEventMass ends C p q A <= indexedBcEventMass ends C' p q A := by
-- proof
  apply StatMech.FK.indexedBcEventMass_mono_bc ends C C' hCC' hp hp1 hq hA


-- created on 2026-10-23
