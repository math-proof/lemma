import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.ListColoring
open SimpleGraph


/--
[IsListColorable.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ListColoring.lean)
-/
@[path]
private lemma IsListColorable_mono_eq
  {G : SimpleGraph V}
  {q r : ℕ}
-- given
  (hG : G.IsListColorable q)
  (hqr : q ≤ r) :
-- imply
  G.IsListColorable r := by
-- proof
  apply SimpleGraph.IsListColorable.mono hG hqr

/--
[IsListColorable.colorable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ListColoring.lean)
-/
@[path]
private lemma IsListColorable_colorable_eq
  {G : SimpleGraph V}
  {q r : ℕ}
-- given
  (hG : G.IsListColorable q) :
-- imply
  G.Colorable q := by
-- proof
  apply SimpleGraph.IsListColorable.colorable hG


-- created on 2026-10-20
