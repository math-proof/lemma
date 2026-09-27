import sympy.stats.iterates
import sympy.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
open Finset Preorder


@[main]
private lemma main
  {d : ℕ}
  {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {x : ℕ → (ℕ → S × S) → EuclideanVec d}
  {x₀ : EuclideanVec d}
  {α : ℕ → ℝ}
  {F : EuclideanVec d → S × S → EuclideanVec d}
-- given
  (h : IteratesOfResidual x x₀ α F) :
-- imply
  AdaptedOnSamplePath x := by
-- proof
  refine ⟨fun n => ?_⟩
  induction n with
  | zero => exact ⟨fun _ => x₀, measurable_const, fun ω => h.init ω⟩
  | succ n ih =>
    obtain ⟨xn, -, hxn⟩ := ih
    let r := frestrictLe₂ (π := fun _ : ℕ => S × S) (Nat.le_succ n)
    refine ⟨fun ω => xn (r ω) + α n • (F (xn (r ω)) (ω ⟨n + 1, by simp⟩) - xn (r ω)),
      measurable_of_finite _, fun ω => ?_⟩
    rw [h.step, hxn]
    rfl


-- created on 2026-09-26