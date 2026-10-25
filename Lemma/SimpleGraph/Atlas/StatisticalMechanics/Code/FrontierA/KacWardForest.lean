import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[kwGraphTransition_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardForest.lean)
-/
@[path]
private lemma kwGraphTransition_support_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : Sym2 V -> ℂ}
  {phase : G.Dart -> G.Dart -> ℂ}
  {d e : G.Dart}
-- given
  (h : kwGraphTransition G x phase d e ≠ 0) :
-- imply
  G.DartAdj d e ∧ d.edge ≠ e.edge := by
-- proof
  apply StatMech.FrontierA.kwGraphTransition_support h

/--
[kwForest_no_long_dart_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardForest.lean)
-/
@[path]
private lemma kwForest_no_long_dart_chain_eq
  [Fintype V]
  {G : SimpleGraph V}
-- given
  (hG : G.IsAcyclic)
  (q : Fin (Fintype.card V + 1) -> G.Dart)
  (hadj : ∀ k : Fin (Fintype.card V), G.DartAdj (q k.castSucc) (q k.succ))
  (hnb : ∀ k : Fin (Fintype.card V), (q k.castSucc).edge ≠ (q k.succ).edge) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierA.kwForest_no_long_dart_chain G hG q hadj hnb

/--
[kwGraphTransition_isNilpotent_of_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardForest.lean)
-/
@[path]
private lemma kwGraphTransition_isNilpotent_of_isAcyclic_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hG : G.IsAcyclic)
  (x : Sym2 V -> ℂ)
  (phase : G.Dart -> G.Dart -> ℂ) :
-- imply
  IsNilpotent (kwGraphTransition G x phase) := by
-- proof
  apply StatMech.FrontierA.kwGraphTransition_isNilpotent_of_isAcyclic G hG x phase

/--
[kwGraphTransition_det_of_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardForest.lean)
-/
@[path]
private lemma kwGraphTransition_det_of_isAcyclic_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hG : G.IsAcyclic)
  (x : Sym2 V -> ℂ)
  (phase : G.Dart -> G.Dart -> ℂ) :
-- imply
  (1 - kwGraphTransition G x phase).det = 1 := by
-- proof
  apply StatMech.FrontierA.kwGraphTransition_det_of_isAcyclic G hG x phase

/--
[kacWard_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardForest.lean)
-/
@[path]
private lemma kacWard_forest_eq
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hG : G.IsAcyclic)
  (x : Sym2 V -> ℂ)
  (phase : G.Dart -> G.Dart -> ℂ) :
-- imply
  (1 - kwGraphTransition G x phase).det = (kwEvenPolynomial G x) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_forest G hG x phase


-- created on 2026-10-23
