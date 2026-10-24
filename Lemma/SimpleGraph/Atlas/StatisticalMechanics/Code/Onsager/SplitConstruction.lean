import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SplitConstruction
open StatMech StatMech.Onsager StatMech.Onsager.SplitConstruction


/--
[arc_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean)
-/
@[path]
private lemma arc_length_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (hb : b < V.length)
  (hab : a ≤ b) :
-- imply
  (arc V a b).length = b - a + 1 := by
-- proof
  apply StatMech.Onsager.SplitConstruction.arc_length V a b hb hab

/--
[coarc_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean)
-/
@[path]
private lemma coarc_length_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (hb : b < V.length)
  (hab : a < b) :
-- imply
  (coarc V a b).length = V.length - b + a + 1 := by
-- proof
  apply StatMech.Onsager.SplitConstruction.coarc_length V a b hb hab

/--
[split_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean)
-/
@[path]
private lemma split_length_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (hb : b < V.length)
  (hab : a < b) :
-- imply
  (arc V a b).length + (coarc V a b).length = V.length + 2 := by
-- proof
  apply StatMech.Onsager.SplitConstruction.split_length V a b hb hab

/--
[arc_length_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean)
-/
@[path]
private lemma arc_length_lt_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (hb : b < V.length)
  (hab : a < b)
  (hstrict : 0 < a ∨ b + 1 < V.length) :
-- imply
  (arc V a b).length < V.length := by
-- proof
  apply StatMech.Onsager.SplitConstruction.arc_length_lt V a b hb hab hstrict

/--
[coarc_length_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean)
-/
@[path]
private lemma coarc_length_lt_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (hb : b < V.length)
  (hab : a + 1 < b) :
-- imply
  (coarc V a b).length < V.length := by
-- proof
  apply StatMech.Onsager.SplitConstruction.coarc_length_lt V a b hb hab

/--
[arc_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean)
-/
@[path]
private lemma arc_nodup_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (h : V.Nodup) :
-- imply
  (arc V a b).Nodup := by
-- proof
  apply StatMech.Onsager.SplitConstruction.arc_nodup V a b h

/--
[coarc_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean)
-/
@[path]
private lemma coarc_disjoint_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (h : V.Nodup)
  (hab : a < b) :
-- imply
  ∀ x ∈ V.drop b, ∀ y ∈ V.take (a + 1), x ≠ y := by
-- proof
  apply StatMech.Onsager.SplitConstruction.coarc_disjoint V a b h hab

/--
[coarc_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean)
-/
@[path]
private lemma coarc_nodup_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (h : V.Nodup)
  (hab : a < b) :
-- imply
  (coarc V a b).Nodup := by
-- proof
  apply StatMech.Onsager.SplitConstruction.coarc_nodup V a b h hab

/--
[arc_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean)
-/
@[path]
private lemma arc_head_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (hab : a ≤ b) :
-- imply
  (arc V a b).head? = V[a]? := by
-- proof
  apply StatMech.Onsager.SplitConstruction.arc_head V a b hab

/--
[arc_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean)
-/
@[path]
private lemma arc_getLast_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (hb : b < V.length)
  (hab : a ≤ b) :
-- imply
  (arc V a b).getLast? = V[b]? := by
-- proof
  apply StatMech.Onsager.SplitConstruction.arc_getLast V a b hb hab

/--
[coarc_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean)
-/
@[path]
private lemma coarc_head_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (hb : b < V.length) :
-- imply
  (coarc V a b).head? = V[b]? := by
-- proof
  apply StatMech.Onsager.SplitConstruction.coarc_head V a b hb

/--
[coarc_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean)
-/
@[path]
private lemma coarc_getLast_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (ha : a < V.length) :
-- imply
  (coarc V a b).getLast? = V[a]? := by
-- proof
  apply StatMech.Onsager.SplitConstruction.coarc_getLast V a b ha

/--
[arc_isClosedWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean)
-/
@[path]
private lemma arc_isClosedWalk_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (hb : b < V.length)
  (hab : a ≤ b)
  (hV : List.IsChain isAxisAligned V)
  (hchord : isAxisAligned V[b] V[a]) :
-- imply
  IsClosedWalk isAxisAligned (arc V a b) := by
-- proof
  apply StatMech.Onsager.SplitConstruction.arc_isClosedWalk V a b hb hab hV hchord

/--
[coarc_isClosedWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean)
-/
@[path]
private lemma coarc_isClosedWalk_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (hb : b < V.length)
  (hab : a < b)
  (hV : List.IsChain isAxisAligned V)
  (hVwrap : ∀ x ∈ V.getLast?, ∀ y ∈ V.head?, isAxisAligned x y)
  (hchord : isAxisAligned V[a] V[b]) :
-- imply
  IsClosedWalk isAxisAligned (coarc V a b) := by
-- proof
  apply StatMech.Onsager.SplitConstruction.coarc_isClosedWalk V a b hb hab hV hVwrap hchord


-- created on 2026-10-23
