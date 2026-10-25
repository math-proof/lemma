import Mathlib
import Mathlib.Data.Real.Sign
import Abbrev.Analysis.Section_9_3.Part2
import Theorem.Analysis.Section_9_4.Part2
import Abbrev.Analysis.Section_9_5
/-!
# Analysis I, Section 9.5: Left and right limits

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Left and right limits.
-/


namespace Chapter9

theorem right_limit.eq {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ .Ioi x₀))
  (h: (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds L)) : RightLimitExists X f x₀ ∧ right_limit X f x₀ = L := by
  have h' : RightLimitExists X f x₀ := by use L
  simp [right_limit, h']
  have hne : (nhdsWithin x₀ (X ∩ .Ioi x₀)).NeBot := by
    rwa [←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

theorem left_limit.eq {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ .Iio x₀))
  (h: (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds L)) : LeftLimitExists X f x₀ ∧ left_limit X f x₀ = L := by
  have h' : LeftLimitExists X f x₀ := by use L
  simp [left_limit, h']
  have hne : (nhdsWithin x₀ (X ∩ .Iio x₀)).NeBot := by
    rwa [←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

theorem right_limit.eq' {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: RightLimitExists X f x₀) :
  (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds (right_limit X f x₀)) := by
  simp [right_limit, h]; exact h.choose_spec

theorem left_limit.eq' {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: LeftLimitExists X f x₀) :
  (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds (left_limit X f x₀)) := by
  simp [left_limit, h]; exact h.choose_spec

theorem right_limit.conv {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (had: AdherentPt x₀ (X ∩ .Ioi x₀))
  (h: RightLimitExists X f x₀)
  (a:ℕ → ℝ) (ha: ∀ n, a n ∈ X ∩ .Ioi x₀)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (right_limit X f x₀)) := by
  choose L hL using h
  apply Convergesto.comp _ ha hconv
  rwa [Convergesto.iff, (eq had hL).2]

theorem left_limit.conv {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (had: AdherentPt x₀ (X ∩ .Iio x₀))
  (h: LeftLimitExists X f x₀)
  (a:ℕ → ℝ) (ha: ∀ n, a n ∈ X ∩ .Iio x₀)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (left_limit X f x₀)) := by
  choose L hL using h
  apply Convergesto.comp _ ha hconv
  rwa [Convergesto.iff, (eq had hL).2]

end Chapter9
