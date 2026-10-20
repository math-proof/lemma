import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Coloring.Vertex
open SimpleGraph


/--
[not_isCritical_of_fintype_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
private lemma not_isCritical_of_fintype_lt_eq
  [Fintype V]
  {G : SimpleGraph V}
  {G}
  {k : ℕ}
-- given
  (hk : Fintype.card V < k) :
-- imply
  ¬G.IsCritical k := by
-- proof
  apply SimpleGraph.not_isCritical_of_fintype_lt G k hk

/--
[colorable_iff_induce_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
private lemma colorable_iff_induce_eq_bot_eq
  {G}
  {G : SimpleGraph V}
  {n : ℕ} :
-- imply
  G.Colorable n ↔ ∃ coloring : V → Fin n, ∀ i, G.induce {v | coloring v = i} = ⊥ := by
-- proof
  apply SimpleGraph.colorable_iff_induce_eq_bot G G n

/--
[Colorable.cocolorable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
private lemma Colorable_cocolorable_eq
  {G : SimpleGraph V}
  {G}
  {n : ℕ}
-- given
  (hc : G.Colorable n) :
-- imply
  G.Cocolorable n := by
-- proof
  apply SimpleGraph.Colorable.cocolorable G hc

/--
[cocolorable_of_fintype](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
private lemma cocolorable_of_fintype_eq
  [Fintype V]
  {G}
  {G : SimpleGraph V} :
-- imply
  G.Cocolorable (Fintype.card V) := by
-- proof
  apply SimpleGraph.cocolorable_of_fintype G G

/--
[Cocolorable.cochromaticNumber_eq_sInf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
private lemma Cocolorable_cochromaticNumber_eq_sInf_eq
  {G : SimpleGraph V}
  {G}
  {n : ℕ}
-- given
  (h : G.Cocolorable n) :
-- imply
  G.cochromaticNumber = sInf {n' : ℕ | G.Cocolorable n'} := by
-- proof
  apply SimpleGraph.Cocolorable.cochromaticNumber_eq_sInf G h

/--
[cochromaticNumber_toNat_eq_sInf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
private lemma cochromaticNumber_toNat_eq_sInf_eq
  [Fintype V]
  {n : ℕ}
  {G}
  {G : SimpleGraph V} :
-- imply
  G.cochromaticNumber.toNat = sInf {n : ℕ | G.Cocolorable n} := by
-- proof
  apply SimpleGraph.cochromaticNumber_toNat_eq_sInf G G

/--
[indepNumK_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
-/
@[path]
private lemma indepNumK_le_card_eq
  [Fintype V]
  {G}
  {G : SimpleGraph V}
  {k : ℕ} :
-- imply
  indepNumK G k ≤ Fintype.card V := by
-- proof
  apply SimpleGraph.indepNumK_le_card G G k


-- created on 2026-10-20
