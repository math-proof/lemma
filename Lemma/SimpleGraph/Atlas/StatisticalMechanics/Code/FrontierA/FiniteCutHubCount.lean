import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteCutHubCount
open Finset Set SimpleGraph StatMech StatMech.FrontierA


/--
[finite_cutHub_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteCutHubCount.lean)
-/
@[path]
private lemma finite_cutHub_count_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hGac : G.IsAcyclic)
  (hubs boundary : Finset V)
  (harms : ∀ u ∈ hubs, ∃ t1 t2 t3 : V, t1 ∈ boundary ∧ t2 ∈ boundary ∧ t3 ∈ boundary ∧ u ≠ t1 ∧ u ≠ t2 ∧ u ≠ t3 ∧ G.Reachable u t1 ∧ G.Reachable u t2 ∧ G.Reachable u t3 ∧ ¬ (G.deleteIncidenceSet u).Reachable t1 t2 ∧ ¬ (G.deleteIncidenceSet u).Reachable t1 t3 ∧ ¬ (G.deleteIncidenceSet u).Reachable t2 t3) :
-- imply
  hubs.card ≤ boundary.card := by
-- proof
  apply StatMech.FrontierA.finite_cutHub_count G hGac hubs boundary harms

/--
[finite_cutHub_count_of_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteCutHubCount.lean)
-/
@[path]
private lemma finite_cutHub_count_of_ambient_eq
  [DecidableEq V]
  {A : SimpleGraph V}
  [DecidableRel A.Adj]
-- given
  (hubs boundary : Finset V)
  (harms : ∀ u ∈ hubs, ∃ t1 t2 t3 : V, t1 ∈ boundary ∧ t2 ∈ boundary ∧ t3 ∈ boundary ∧ u ≠ t1 ∧ u ≠ t2 ∧ u ≠ t3 ∧ A.Reachable u t1 ∧ A.Reachable u t2 ∧ A.Reachable u t3 ∧ ¬ (A.deleteIncidenceSet u).Reachable t1 t2 ∧ ¬ (A.deleteIncidenceSet u).Reachable t1 t3 ∧ ¬ (A.deleteIncidenceSet u).Reachable t2 t3) :
-- imply
  hubs.card ≤ boundary.card := by
-- proof
  apply StatMech.FrontierA.finite_cutHub_count_of_ambient A hubs boundary harms


-- created on 2026-10-23
