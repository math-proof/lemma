import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.InequalitiesMenger.Part3
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[finiteABSeparators_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/InequalitiesMenger.lean)
-/
@[path]
private lemma finiteABSeparators_nonempty_eq
  [Fintype V]
  {G : SimpleGraph V}
  {A B : Set V} :
-- imply
  (finiteABSeparators G A B).Nonempty := by
-- proof
  apply StatMech.FrontierA.finiteABSeparators_nonempty G A B

/--
[finiteABPackingSizes_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/InequalitiesMenger.lean)
-/
@[path]
private lemma finiteABPackingSizes_nonempty_eq
  [Fintype V]
  {G : SimpleGraph V}
  {A B : Set V} :
-- imply
  (finiteABPackingSizes G A B).Nonempty := by
-- proof
  apply StatMech.FrontierA.finiteABPackingSizes_nonempty G A B

/--
[finite_vertex_menger_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/InequalitiesMenger.lean)
-/
@[path]
private lemma finite_vertex_menger_threshold_eq
  [Fintype V]
  {G : SimpleGraph V}
  {A B : Set V}
  {k : ℕ}
-- given
  (_hAB : Disjoint A B) :
-- imply
  Nonempty (bc16_DisjointPathFamily G A B (Fin k)) ↔ ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard := by
-- proof
  apply StatMech.FrontierA.finite_vertex_menger_threshold G A B _hAB k

/--
[finite_vertex_menger](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/InequalitiesMenger.lean)
-/
@[path]
private lemma finite_vertex_menger_eq
  [Fintype V]
  {G : SimpleGraph V}
  {A B : Set V}
-- given
  (_hAB : Disjoint A B) :
-- imply
  vertexDisjointPathNumber G A B = vertexSeparatorNumber G A B := by
-- proof
  apply StatMech.FrontierA.finite_vertex_menger G A B _hAB


-- created on 2026-10-23
