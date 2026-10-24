/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Calculus/Bisection.lean -/


import sympy.atlas.Analysis.Calculus.Bisection
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Ring.Real

-- Constant-positive bisection sequences stay ordered without bracketing a root.
example :
    ∃ u v : ℕ → ℝ,
      MetaMathlibExt.IsBisectionSequence (fun _ => (1 : ℝ)) 0 1 u v ∧ u 1 ≤ v 1 := by
  obtain ⟨u, v, hseq⟩ :=
    MetaMathlibExt.exists_isBisectionSequence (fun _ => (1 : ℝ)) 0 1
  refine ⟨u, v, hseq, ?_⟩
  exact (hseq.nested (by norm_num) 0).2.1

-- Constant-positive bisection midpoints stay inside `[0, 1]` without bracketing a root.
example :
    ∃ u v : ℕ → ℝ,
      MetaMathlibExt.IsBisectionSequence (fun _ => (1 : ℝ)) 0 1 u v ∧
        ∀ n, (u n + v n) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨u, v, hseq⟩ :=
    MetaMathlibExt.exists_isBisectionSequence (fun _ => (1 : ℝ)) 0 1
  refine ⟨u, v, hseq, ?_⟩
  intro n
  obtain ⟨hu, huv, hv⟩ := hseq.le_and_le (by norm_num) n
  constructor <;> linarith

-- Bisection of `x² - 2` on `[0, 2]` gives a root with the explicit midpoint rate.
example :
    ∃ u v : ℕ → ℝ,
      MetaMathlibExt.IsBisectionSequence (fun x : ℝ => x ^ 2 - 2) 0 2 u v ∧
      ∃ c ∈ Set.Icc (0 : ℝ) 2, c ^ 2 = 2 ∧
        Filter.Tendsto (fun n => (u n + v n) / 2) Filter.atTop (nhds c) ∧
        ∀ n, |(u n + v n) / 2 - c| ≤ 2 / (2 : ℝ) ^ (n + 1) := by
  have hab : (0 : ℝ) ≤ 2 := by norm_num
  have hf : ContinuousOn (fun x : ℝ => x ^ 2 - 2) (Set.Icc 0 2) :=
    ((continuous_id.pow 2).sub continuous_const).continuousOn
  have ha : (fun x : ℝ => x ^ 2 - 2) 0 ≤ 0 := by norm_num
  have hb : 0 ≤ (fun x : ℝ => x ^ 2 - 2) 2 := by norm_num
  obtain ⟨u, v, hseq, -, -, -⟩ :=
    MetaMathlibExt.bisection_nested_intervals hab hf ha hb
  obtain ⟨c, hc, hroot, htend, herr⟩ :=
    MetaMathlibExt.bisection_approximate_root_with_rate hab hf ha hb u v hseq
  refine ⟨u, v, hseq, c, hc, ?_, htend, ?_⟩
  · linarith
  · intro n
    simpa using herr n

-- The tenth bisection midpoint approximates `√2` within one thousandth.
example (u v : ℕ → ℝ)
    (hseq : MetaMathlibExt.IsBisectionSequence (fun x : ℝ => x ^ 2 - 2) 0 2 u v) :
    |(u 10 + v 10) / 2 - Real.sqrt 2| ≤ 1 / 1000 := by
  have hab : (0 : ℝ) ≤ 2 := by norm_num
  have hf : ContinuousOn (fun x : ℝ => x ^ 2 - 2) (Set.Icc 0 2) :=
    ((continuous_id.pow 2).sub continuous_const).continuousOn
  have ha : (fun x : ℝ => x ^ 2 - 2) 0 ≤ 0 := by norm_num
  have hb : 0 ≤ (fun x : ℝ => x ^ 2 - 2) 2 := by norm_num
  obtain ⟨c, hc, hroot, -, herr⟩ :=
    MetaMathlibExt.bisection_approximate_root_with_rate hab hf ha hb u v hseq
  have hc_sq : c ^ 2 = 2 := by linarith
  have hc_eq : c = Real.sqrt 2 := by
    symm
    exact (Real.sqrt_eq_iff_eq_sq (by norm_num) hc.1).2 hc_sq.symm
  calc
    |(u 10 + v 10) / 2 - Real.sqrt 2| = |(u 10 + v 10) / 2 - c| := by rw [hc_eq]
    _ ≤ 2 / (2 : ℝ) ^ (10 + 1) := by simpa using herr 10
    _ ≤ 1 / 1000 := by norm_num

-- Bisection brackets a jump and halves its interval without any continuity assumption.
example (u v : ℕ → ℝ)
    (hseq : MetaMathlibExt.IsBisectionSequence
      (fun x : ℝ => if x < 1 / 3 then (-1 : ℝ) else 1) 0 1 u v) (n : ℕ) :
    u n < 1 / 3 ∧ 1 / 3 ≤ v n ∧ v n - u n = 1 / (2 : ℝ) ^ n := by
  have hinv := hseq.invariants (by norm_num) (by norm_num) (by norm_num) n
  have hu : u n < 1 / 3 := by
    by_contra h
    have hfu := hinv.2.2.2.1
    rw [ite_eq_right h] at hfu
    norm_num at hfu
  have hv : 1 / 3 ≤ v n := by
    by_contra h
    push Not at h
    have hfv := hinv.2.2.2.2
    rw [ite_eq_left h] at hfv
    norm_num at hfv
  exact ⟨hu, hv, by simpa using hseq.sub_eq n⟩

-- The continuity-free theorem constructs nested intervals that locate the same jump.
example :
    ∃ u v : ℕ → ℝ,
      MetaMathlibExt.IsBisectionSequence
          (fun x : ℝ => if x < 1 / 3 then (-1 : ℝ) else 1) 0 1 u v ∧
        (∀ n, u n ≤ u (n + 1) ∧ u (n + 1) ≤ v (n + 1) ∧ v (n + 1) ≤ v n) ∧
        (∀ n, v n - u n = 1 / (2 : ℝ) ^ n) ∧
        ∀ n, u n < 1 / 3 ∧ 1 / 3 ≤ v n := by
  obtain ⟨u, v, hseq, hnested, hlength, -⟩ :=
    MetaMathlibExt.exists_isBisectionSequence_nested
      (f := fun x : ℝ => if x < 1 / 3 then (-1 : ℝ) else 1)
      (a := 0) (b := 1) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨u, v, hseq, hnested, ?_, ?_⟩
  · intro n
    simpa using hlength n
  · intro n
    have hinv := hseq.invariants (by norm_num) (by norm_num) (by norm_num) n
    constructor
    · by_contra h
      have hfu := hinv.2.2.2.1
      rw [ite_eq_right h] at hfu
      norm_num at hfu
    · by_contra h
      push Not at h
      have hfv := hinv.2.2.2.2
      rw [ite_eq_left h] at hfv
      norm_num at hfv
