import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.EvenSubgraphDecomp
open Finset SimpleGraph StatMech StatMech.Ising StatMech.Ising.EvenSubgraphDecomp


/--
[core_exists_closed_eulerian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/EvenSubgraphDecomp.lean)
-/
@[path]
private lemma core_exists_closed_eulerian_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u : V}
-- given
  (hconn : G.Connected)
  (heven : ∀ x, Even (G.degree x)) :
-- imply
  ∃ p : G.Walk u u, p.IsTrail ∧ ∀ e ∈ G.edgeFinset, e ∈ p.edges := by
-- proof
  apply StatMech.Ising.EvenSubgraphDecomp.core_exists_closed_eulerian G hconn heven u

/--
[subgraphF_degree_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/EvenSubgraphDecomp.lean)
-/
@[path]
private lemma subgraphF_degree_even_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {v : V}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag)
  (hev : IsEvenSubgraph F) :
-- imply
  Even ((subgraphF F).degree v) := by
-- proof
  apply StatMech.Ising.EvenSubgraphDecomp.subgraphF_degree_even F hF hev v

/--
[evenSubgraphWalkDecomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/EvenSubgraphDecomp.lean)
-/
@[path]
private lemma evenSubgraphWalkDecomp_eq
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {Gd : SimpleGraph V}
  [DecidableRel Gd.Adj] :
-- imply
  EvenSubgraphWalkDecomp Gd := by
-- proof
  apply StatMech.Ising.evenSubgraphWalkDecomp Gd


-- created on 2026-10-23
