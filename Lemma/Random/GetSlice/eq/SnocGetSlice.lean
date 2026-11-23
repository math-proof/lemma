import Instance.Probability.Process.HiddenMarkovSequence
import Instance.Data.Nat.Fun
import Initialize.Tactic.Attr.Basic
open Fun


/--
The length-`(t + 1)` prefix of a process is the snoc of its length-`t` prefix
and the current entry, pointwise.
-/
@[path]
private lemma main
  {s : ℕ → Ω → α}
-- given
  (t : ℕ) (ω : Ω) :
-- imply
  (s[:t.succ] : Ω → Fin t.succ → α) ω =
    Fin.snoc ((s[:t] : Ω → Fin t → α) ω) (s[t] ω) := by
-- proof
  ext i
  refine Fin.lastCases ?_ ?_ i
  ·
    simp [Function.getSlice, FunSlice.slice, Fin.snoc_last,
      Fin.val_last, Int.toNat_natCast]
  ·
    intro j
    simp [Function.getSlice, FunSlice.slice, Fin.snoc_castSucc,
      Int.toNat_natCast]


-- created on 2026-11-19
-- updated on 2026-11-23
