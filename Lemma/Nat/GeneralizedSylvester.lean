import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GeneralizedSylvester
open Nat


/--
[generalizedSylvester_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedSylvester.lean)
-/
@[path]
private lemma generalizedSylvester_zero_eq
  {n : ℕ} :
-- imply
  generalizedSylvester n 0 = n + 1 := by
-- proof
  apply Nat.generalizedSylvester_zero n

/--
[generalizedSylvester_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedSylvester.lean)
-/
@[path]
private lemma generalizedSylvester_succ_eq
  {n k : ℕ} :
-- imply
  generalizedSylvester n (k + 1) =
      generalizedSylvester n k ^ 2 - generalizedSylvester n k + 1 := by
-- proof
  apply Nat.generalizedSylvester_succ n k

/--
[generalizedSylvester_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedSylvester.lean)
-/
@[path]
private lemma generalizedSylvester_pos_eq
  {n k : ℕ} :
-- imply
  0 < generalizedSylvester n k := by
-- proof
  apply Nat.generalizedSylvester_pos n k


-- created on 2026-10-20
