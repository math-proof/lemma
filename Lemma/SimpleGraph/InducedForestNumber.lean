import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.InducedForestNumber
open SimpleGraph


/--
[card_le_inducedForestNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/InducedForestNumber.lean)
-/
@[path]
private lemma card_le_inducedForestNumber_eq
  [Fintype V]
  {G : SimpleGraph V}
  {s : Finset V}
-- given
  (h : (G.induce (↑s : Set V)).IsAcyclic) :
-- imply
  s.card ≤ G.inducedForestNumber := by
-- proof
  apply SimpleGraph.card_le_inducedForestNumber G s h

/--
[inducedForestNumber_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/InducedForestNumber.lean)
-/
@[path]
private lemma inducedForestNumber_le_card_eq
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  G.inducedForestNumber ≤ Fintype.card V := by
-- proof
  apply SimpleGraph.inducedForestNumber_le_card G

/--
[exists_isAcyclic_card_eq_inducedForestNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/InducedForestNumber.lean)
-/
@[path]
private lemma exists_isAcyclic_card_eq_inducedForestNumber_eq
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  ∃ s : Finset V, (G.induce (↑s : Set V)).IsAcyclic ∧ s.card = G.inducedForestNumber := by
-- proof
  apply SimpleGraph.exists_isAcyclic_card_eq_inducedForestNumber G


-- created on 2026-10-20
