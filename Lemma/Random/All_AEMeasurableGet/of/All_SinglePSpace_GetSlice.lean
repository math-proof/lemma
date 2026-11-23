import Instance.Probability.Process.HiddenMarkovSequence
import Syntax.Data.List
import Notation.Fun
import Initialize.Tactic.Attr.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Instance.Data.Nat.Fun
open MeasureTheory


/--
Every coordinate `s[k]` is almost everywhere measurable whenever every process
prefix `s[:n]` carries a density. Indeed `s[k]` is the projection of `s[:k.succ]`
onto a single coordinate, and measurability of that projection composes with the
a.e. measurability supplied by the `SinglePSpace` hypothesis.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → 𝒮}
-- given
  (hP : ∀ n, SinglePSpace π (s[:n] : Ω → Fin n → 𝒮)) :
-- imply
  ∀ k : ℕ, AEMeasurable s[k] π := by
-- proof
  intro k
  let i : Fin k.succ := ⟨k, Nat.lt_succ_self k⟩
  have heq : ((fun f : Fin k.succ → 𝒮 => f i) ∘ s[:k.succ]) = s[k] := by
    funext ω
    simp [Function.getSlice, FunSlice.slice, Int.toNat_zero]
    rfl
  have h := (measurable_pi_apply i).comp_aemeasurable (hP k.succ).aemeasurable
  rwa [heq] at h


-- created on 2026-11-19
