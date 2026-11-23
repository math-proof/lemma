import Mathlib.Probability.Independence.Basic
import Notation.Fun
import Instance.Data.Nat.Fun
import Instance.Probability.Process.HiddenMarkovSequence
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Fun


/--
Sequential independence of each term from its past implies pairwise independence.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → ℝ}
-- given
  (h₀ : ∀ (k : ℕ), x[k] ⟂ᵢ[π] x[:k]) :
-- imply
  ∀ (i j : ℕ) (_ : i ≠ j), x[i] ⟂ᵢ[π] x[j] := by
-- proof
  intro i j hij
  wlog hlt : i < j generalizing i j
  · exact (this j i hij.symm (hij.lt_or_gt.resolve_left hlt)).symm
  have hx : (fun ω => x[:j] ω ⟨i, hlt⟩) = x[i] := by
    funext ω
    simp [Function.getSlice, FunSlice.slice, Int.toNat_zero]
  have hproj : x[j] ⟂ᵢ[π] (fun ω => x[:j] ω ⟨i, hlt⟩) :=
    (h₀ j).comp measurable_id (measurable_pi_apply _)
  simpa [hx] using hproj.symm


-- created on 2026-11-03
-- updated on 2026-11-23
