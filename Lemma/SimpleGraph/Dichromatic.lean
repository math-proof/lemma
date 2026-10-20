import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Dichromatic
open SimpleGraph


/--
[DichromaticColorable.dichromaticNumber_eq_sInf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Dichromatic.lean)
-/
@[path]
private lemma DichromaticColorable_dichromaticNumber_eq_sInf_eq
  {G : SimpleGraph V}
  {n : ℕ}
-- given
  (h : G.DichromaticColorable n) :
-- imply
  G.dichromaticNumber = sInf {n' : ℕ | G.DichromaticColorable n'} := by
-- proof
  apply SimpleGraph.DichromaticColorable.dichromaticNumber_eq_sInf G h

/--
[IsOrientation.of_edgeless](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Dichromatic.lean)
-/
@[path]
private lemma IsOrientation_of_edgeless_eq
  {G : SimpleGraph V}
-- given
  (hempty : ∀ u v, ¬ G.Adj u v) :
-- imply
  G.IsOrientation (fun _ _ => False) := by
-- proof
  apply SimpleGraph.IsOrientation.of_edgeless G hempty

/--
[DichromaticColorable.of_edgeless](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Dichromatic.lean)
-/
@[path]
private lemma DichromaticColorable_of_edgeless_eq
  {G : SimpleGraph V}
-- given
  (hempty : ∀ u v, ¬ G.Adj u v) :
-- imply
  G.DichromaticColorable 1 := by
-- proof
  apply SimpleGraph.DichromaticColorable.of_edgeless G hempty


-- created on 2026-10-20
