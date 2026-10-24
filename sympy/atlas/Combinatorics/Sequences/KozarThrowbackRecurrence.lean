/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean -/

import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Push

namespace MetaMathlibExt

section

private def tbStep (Y : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < Y 0 then Y (i + 1) else if i = Y 0 then Y 0 else Y i

private def tbX : ℕ → ℕ := fun i => i + 3

private def Yseq (k : ℕ) : ℕ → ℕ := Nat.iterate tbStep k tbX
end
end MetaMathlibExt
