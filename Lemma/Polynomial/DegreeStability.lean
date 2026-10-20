import Mathlib
import sympy.Basic
import sympy.atlas.Algebra.Polynomial.DegreeStability
open Polynomial


/--
[natDegree_eq_of_monic_of_l1Norm_sub_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/DegreeStability.lean)
-/
@[path]
private lemma natDegree_eq_of_monic_of_l1Norm_sub_lt_one_eq
  [Ring K] [Nontrivial K]
  {v : AbsoluteValue K ℝ}
  {f g : Polynomial K}
-- given
  (hf : f.Monic)
  (hg : g.Monic)
  (h : l1Norm v (f - g) < 1) :
-- imply
  f.natDegree = g.natDegree := by
-- proof
  apply Polynomial.natDegree_eq_of_monic_of_l1Norm_sub_lt_one v hf hg h


-- created on 2026-10-20
