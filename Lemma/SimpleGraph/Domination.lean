import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Domination
open SimpleGraph


/--
[exists_isIndepDominating](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Domination.lean)
-/
@[path]
private lemma exists_isIndepDominating_eq
  [Finite V]
  {G : SimpleGraph V} :
-- imply
  ∃ S : Finset V, G.IsIndepDominating ↑S := by
-- proof
  apply SimpleGraph.exists_isIndepDominating G

/--
[exists_indepDominationNumber_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Domination.lean)
-/
@[path]
private lemma exists_indepDominationNumber_eq_card_eq
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  ∃ S : Finset V, S.card = G.indepDominationNumber ∧ G.IsIndepDominating ↑S := by
-- proof
  apply SimpleGraph.exists_indepDominationNumber_eq_card G

/--
[indepDominationNumber_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Domination.lean)
-/
@[path]
private lemma indepDominationNumber_le_card_eq
  [Fintype V]
  {G : SimpleGraph V}
  {S : Finset V}
-- given
  (hS : G.IsIndepDominating ↑S) :
-- imply
  G.indepDominationNumber ≤ S.card := by
-- proof
  apply SimpleGraph.indepDominationNumber_le_card G hS

/--
[exists_dominationNumber_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Domination.lean)
-/
@[path]
private lemma exists_dominationNumber_eq_card_eq
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  ∃ S : Finset V, S.card = G.dominationNumber ∧ G.IsDominating ↑S := by
-- proof
  apply SimpleGraph.exists_dominationNumber_eq_card G

/--
[dominationNumber_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Domination.lean)
-/
@[path]
private lemma dominationNumber_le_card_eq
  [Fintype V]
  {G : SimpleGraph V}
  {S : Finset V}
-- given
  (hS : G.IsDominating ↑S) :
-- imply
  G.dominationNumber ≤ S.card := by
-- proof
  apply SimpleGraph.dominationNumber_le_card G hS


-- created on 2026-10-20
