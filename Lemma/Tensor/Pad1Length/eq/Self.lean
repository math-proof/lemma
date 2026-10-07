import sympy.core.mul
import sympy.Basic
open Tensor


@[main]
private lemma main
-- given
  (s : List ℕ) :
-- imply
  pad1 s s.length = s := by
-- proof
  simp [pad1]


-- created on 2026-10-07
