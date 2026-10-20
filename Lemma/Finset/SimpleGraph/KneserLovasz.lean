import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.KneserLovasz
open Finset
open MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted


/--
[kneserGraph_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma kneserGraph_adj_iff_eq
  {n k : ℕ}
  {x y : KneserVertex n k} :
-- imply
  (kneserGraph n k).Adj x y ↔ Disjoint x.val y.val ∧ x ≠ y := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted.kneserGraph_adj_iff n k x y

/--
[kneser_lovasz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma kneser_lovasz_eq
  {n k : ℕ}
-- given
  (hk : 0 < k)
  (h : 2 * k ≤ n) :
-- imply
  (kneserGraph n k).chromaticNumber = (n - 2 * k + 2 : ℕ∞) := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted.kneser_lovasz hk h


-- created on 2026-10-20
