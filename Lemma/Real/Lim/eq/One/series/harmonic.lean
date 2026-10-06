import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import sympy.series.limits
import sympy.Basic

open scoped Topology
open Filter


@[main]
private lemma main
  :
-- imply
  lim [n → ∞] ((harmonic n : ℝ) / Real.log ((n : ℝ) + 1)) = 1 := by
-- proof
  have hγ :
      Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log ((n : ℝ) + 1)) atTop
        (𝓝 Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log_add_one
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hl : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have hd :
      Tendsto
        (fun n : ℕ =>
          ((harmonic n : ℝ) - Real.log ((n : ℝ) + 1)) / Real.log ((n : ℝ) + 1)) atTop (𝓝 0) :=
    hγ.div_atTop hl
  have heq :
      ∀ᶠ n in atTop,
        (harmonic n : ℝ) / Real.log ((n : ℝ) + 1) =
          1 + ((harmonic n : ℝ) - Real.log ((n : ℝ) + 1)) / Real.log ((n : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have h1 : (n : ℝ) + 1 > 1 := by
      have h2 : (1 : ℝ) ≤ n := by
        rw [← Nat.cast_one]
        exact Nat.cast_le.mpr hn1
      linarith
    have hlp : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos h1
    field_simp [hlp.ne']
    <;> ring
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsum :
      Tendsto (fun n : ℕ => (1 : ℝ) + ((harmonic n : ℝ) - Real.log ((n : ℝ) + 1)) /
        Real.log ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
    hc.add hd
  have ht :
      Tendsto (fun n : ℕ => (harmonic n : ℝ) / Real.log ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
    hsum.congr' (Filter.EventuallyEq.symm heq)
  simpa using ht


-- created on 2020-06-25
