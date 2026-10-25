import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredEndpoints.Part3
open Finset SimpleGraph StatMech StatMech.Universality


/--
[fkIsingSquareWiredArc_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEndpoints.lean)
-/
@[path]
private lemma fkIsingSquareWiredArc_card_eq
  {n : Nat} :
-- imply
  Nat.card {x : (fkSquareBoxPlanar n).V // fkIsingSquareWiredArc n x} = 2 * n + 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredArc_card n

/--
[fkIsingSquareWired_empty_clusterCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEndpoints.lean)
-/
@[path]
private lemma fkIsingSquareWired_empty_clusterCount_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  numClustersBC (fkSquareBoxPlanar n).G (fkIsingSquareWiredDobrushinDomain n hn).wiring (FK.edgeSetConfig ∅) = (2 * n + 1) ^ 2 - 2 * n := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_empty_clusterCount n hn

/--
[fkIsingSquareWired_full_clusterCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEndpoints.lean)
-/
@[path]
private lemma fkIsingSquareWired_full_clusterCount_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  numClustersBC (fkSquareBoxPlanar n).G (fkIsingSquareWiredDobrushinDomain n hn).wiring (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_full_clusterCount n hn

/--
[fkIsingSquareWired_full_openCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEndpoints.lean)
-/
@[path]
private lemma fkIsingSquareWired_full_openCount_eq
  {n : Nat} :
-- imply
  openCount (fkSquareBoxPlanar n).G (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) = 2 * ((2 * n) * (2 * n + 1)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_full_openCount n

/--
[fkIsingSquareWired_empty_openCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEndpoints.lean)
-/
@[path]
private lemma fkIsingSquareWired_empty_openCount_eq
  {n : Nat} :
-- imply
  openCount (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_empty_openCount n

/--
[fkIsingSquareWiredEulerDefect_empty_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEndpoints.lean)
-/
@[path]
private lemma fkIsingSquareWiredEulerDefect_empty_formula_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅) = 2 * ((2 * n + 1) ^ 2 - 2 * n) - Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).ConnectedComponent := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredEulerDefect_empty_formula n hn

/--
[fkIsingSquareWiredEulerDefect_full_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEndpoints.lean)
-/
@[path]
private lemma fkIsingSquareWiredEulerDefect_full_formula_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) = 2 * ((2 * n + 1) ^ 2 - 2 * n) - Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredEulerDefect_full_formula n hn

/--
[fkIsingSquareWiredEulerDefect_empty_full_iff_componentCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEndpoints.lean)
-/
@[path]
private lemma fkIsingSquareWiredEulerDefect_empty_full_iff_componentCount_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) = fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅) ↔ Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent = Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).ConnectedComponent := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredEulerDefect_empty_full_iff_componentCount n hn


-- created on 2026-10-23
