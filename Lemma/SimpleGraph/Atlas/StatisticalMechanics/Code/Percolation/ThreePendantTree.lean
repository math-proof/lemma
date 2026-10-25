import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.ThreePendantTree
open Set SimpleGraph Finset StatMech StatMech.Percolation


/--
[three_pendant_vertices_have_tripod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreePendantTree.lean)
-/
@[path]
private lemma three_pendant_vertices_have_tripod_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : Fin 3 → V}
-- given
  (hG : G.Connected)
  (hpinj : Function.Injective p)
  (hpdeg : ∀ i, G.degree (p i) = 1) :
-- imply
  ∃ (C : Set V) (T : SimpleGraph C) (_ : DecidableRel T.Adj) (hub : C) (stem leaf : Fin 3 → C), T.IsTree ∧ (∀ a b, T.Adj a b → G.Adj a.1 b.1) ∧ Function.Injective stem ∧ (∀ i, T.Adj hub (stem i)) ∧ Function.Injective leaf ∧ (∀ i, ∃ j, (leaf i).1 = p j) ∧ (∀ i, (T.deleteIncidenceSet hub).Reachable (stem i) (leaf i)) ∧ (∀ i, T.Reachable hub (leaf i)) ∧ (∀ i j, i ≠ j → ¬ (T.deleteIncidenceSet hub).Reachable (leaf i) (leaf j)) := by
-- proof
  apply StatMech.Percolation.three_pendant_vertices_have_tripod G hG p hpinj hpdeg


-- created on 2026-10-23
