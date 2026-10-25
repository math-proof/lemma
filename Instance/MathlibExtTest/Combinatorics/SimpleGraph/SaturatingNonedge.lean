/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean -/


import Def.Combinatorics.SimpleGraph.SaturatingNonedge
import Lemma.SimpleGraph.SaturatingNonedge
import Mathlib.Tactic.FinCases
open SimpleGraph

/-!
# Boundary tests for `F`-saturating non-edges

Source: Xiaolin Wang, Jiabao Yang, and Ruilin Zheng,
*Clique-saturating non-edges throughout the Turan range*, arXiv:2608.25831v1.
Active source: `main.tex`, lines 89-99.

These tests exercise every public declaration of
`MathlibExt.Combinatorics.SimpleGraph.SaturatingNonedge` against the
source-sensitive boundaries: a single missing edge that creates a copy, a loop
rejection (discriminating for distinctness), an already-present edge rejection
(discriminating for absence), distinct absent endpoints with no created copy
(discriminating for copy containment), symmetry, the new-copy consequence, the
saturating graph, and the finite counts `1` and `0`.
-/


noncomputable local instance instCountOne (G : SimpleGraph (Fin 2)) :
    Fintype G.edgeSet := by
  classical
  exact fintypeEdgeSet _

noncomputable local instance instCountZero (G : SimpleGraph (Fin 2)) :
    Fintype G.edgeSet := by
  classical
  exact fintypeEdgeSet _

