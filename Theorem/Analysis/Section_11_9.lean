import Mathlib
import Mathlib.Topology.ContinuousOn
import Theorem.Analysis.Section_7_3
import Theorem.Analysis.Section_9_4.Part2
import Abbrev.Analysis.Section_9_8
import Theorem.Analysis.Section_10_1.Part2
import Abbrev.Analysis.Section_10_2
import Theorem.Analysis.Section_11_6
import Abbrev.Analysis.Section_11_8.Part7
/-!
# Analysis I, Section 11.9: The two fundamental theorems of calculus

I have attempted to make the translation as faithful a paraphrasing as possible of the
original text. When there is a choice between a more idiomatic Lean solution and a
more faithful translation, I have generally chosen the latter. In particular, there will
be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I
have consciously avoided doing so.

Main constructions and results of this section:
- The fundamental theorems of calculus.
-/


namespace Chapter11

open Chapter9 Chapter10 BoundedInterval

/-- Theorem 11.9.1 (First Fundamental Theorem of Calculus). -/
theorem cts_of_integ {a b:ℝ} {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b)) :
  ContinuousOn (fun x => integ f (Icc a x)) (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  set F : ℝ → ℝ := fun x => integ f (Icc a x)
  choose M hM using hf.1
  have {x y:ℝ} (hxy: x < y) (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) : |F y - F x| ≤ M * (y - x) := by
    simp at hx hy
    have := ((hf.join (join_Icc_Ioc hy.1 hy.2)).1.join (join_Icc_Ioc hx.1 (le_of_lt hxy))).2
    simp [F, this.2, abs_le']
    constructor
    . convert this.1.mono (g := fun _ ↦ M) (IntegrableOn.const _ _).1 _
      . simp [IntegrableOn.const, le_of_lt hxy]
      intro z hz
      specialize hM z ?_
      . simp at *; grind
      grind [abs_le']
    rw [neg_le]
    convert (IntegrableOn.const _ _).1.mono (f := fun _ ↦ -M) this.1 _
    . simp [IntegrableOn.const, le_of_lt hxy]
    intro z hz
    specialize hM z ?_
    . simp at *; grind
    grind [abs_le']
  replace {x y:ℝ} (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) :
    |F y - F x| ≤ M * |x-y| := by
    obtain h | rfl | h := lt_trichotomy x y
    . simp [abs_of_neg (show x-y < 0 by linarith), this h hx hy]
    . simp
    . simp [abs_of_pos (show 0 < x-y by linarith), abs_sub_comm, this h hy hx]
  replace : UniformContinuousOn F (.Icc a b) := by
    simp [Metric.uniformContinuousOn_iff, Real.dist_eq, -Set.mem_Icc]
    intro ε hε
    use (ε/(max M 1)), (by positivity)
    intro x hx y hy hxy
    calc
      _ = |F y - F x| := by rw [abs_sub_comm]
      _ ≤ M * |x-y| := this hx hy
      _ ≤ (max M 1) * |x-y| := by gcongr; apply le_max_left
      _ < (max M 1) * (ε / (max M 1)) := by gcongr
      _ = _ := by field_simp
  exact ContinuousOn.ofUniformContinuousOn F this

/-- Example 11.9.2 -/
theorem IntegrableOn.of_f_9_8_5 : IntegrableOn f_9_8_5 (Icc 0 1) :=
  integ_of_monotone (StrictMonoOn.of_f_9_8_5.mono (by simp)).monotoneOn

end Chapter11
