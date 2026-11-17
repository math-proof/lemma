import Syntax.Data.List
import Notation.Fun
import Instance.Probability.Process.HiddenMarkovSequence
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Fun


/--
A process prefix `s[:k]` is measurable whenever every coordinate `s[i]` is.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace 𝒮]
  {s : ℕ ⇀ Ω → 𝒮}
-- given
  (hs : ∀ k : ℕ, Measurable s[k]) :
-- imply
  ∀ k : ℕ, Measurable s[:k] := by
-- proof
  intro k
  apply Measurable.of_eval
  intro i
  have heq : (fun ω => s[:k] ω i) = s[i] := by
    funext ω
    simp [Fun.getSlice, Function.getSlice, FunSlice.slice, Int.toNat_zero]
    rfl
  rw [heq]
  apply hs


-- created on 2026-11-17
