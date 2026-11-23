import Syntax.Data.List
import Notation.Fun
import Instance.Data.Nat.Fun
import Instance.Probability.Process.HiddenMarkovSequence
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Fun


/--
A process is coordinate-wise measurable if and only if all its prefixes are.
| attributes | lemma |
| :---: | :---: |
| path | Random.All_MeasurableGet.is.All_MeasurableGetSlice |
| mp | Random.All_MeasurableGetSlice.of.All_MeasurableGet |
| mpr | Random.All_MeasurableGet.of.All_MeasurableGetSlice |
-/
@[path, mp, mpr]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace 𝒮]
  {s : ℕ → Ω → 𝒮} :
-- imply
  (∀ k : ℕ, Measurable s[k]) ↔ ∀ k : ℕ, Measurable s[:k] := by
-- proof
  constructor
  ·
    intro hs k
    apply Measurable.of_eval
    intro i
    have heq : (fun ω => s[:k] ω i) = s[i] := by
      funext ω
      simp [Function.getSlice, FunSlice.slice, Int.toNat_zero]
    rw [heq]
    apply hs
  ·
    intro hs k
    have hk : Measurable (fun ω => (s[:k.succ] : Ω → Fin k.succ → 𝒮) ω) := hs k.succ
    have heq : s[k] = fun ω => (s[:k.succ] : Ω → Fin k.succ → 𝒮) ω (Fin.last k) := by
      funext ω
      simp [Function.getSlice, FunSlice.slice, Int.toNat_zero, Fin.val_last]
    rw [heq]
    exact (measurable_pi_apply (Fin.last k)).comp hk


-- created on 2026-11-17
