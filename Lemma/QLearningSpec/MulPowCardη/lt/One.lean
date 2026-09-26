import sympy.stats.q_learning
import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lemma.QLearningSpec.Gtμmin_0AndGeη_0AndLtη_1


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {spec : QLearningSpec S A} :
-- imply
  (Fintype.card (S × A) : ℝ) ^ (1 / (spec.pmin : ℝ)) * spec.η < 1 := by
-- proof
  obtain ⟨-, hη0, hη1⟩ := QLearningSpec.Gtμmin_0AndGeη_0AndLtη_1 (spec := spec)
  have hcard : (1 : ℝ) ≤ Fintype.card (S × A) := by exact_mod_cast Fintype.card_pos
  have hp : spec.pmin_aux < spec.pmin := by
    have h₁ : ((Nat.ceil spec.pmin_aux + 1 : ℕ) : ℝ) ≤ spec.pmin := by exact_mod_cast le_max_right _ _
    push_cast at h₁
    linarith [Nat.le_ceil spec.pmin_aux]
  have hp0 : (0 : ℝ) < spec.pmin := by exact_mod_cast (show 0 < spec.pmin by have : 2 ≤ spec.pmin := le_max_left _ _; omega)
  rcases hη0.eq_or_lt with h | h
  · rw [← h, mul_zero]
    exact one_pos
  rcases hcard.eq_or_lt with hc | hc
  · rw [← hc, Real.one_rpow, one_mul]
    exact hη1
  have hK : 0 < Real.log (1 / spec.η) := Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ h).2 hη1)
  have h₂ : Real.log (Fintype.card (S × A)) / spec.pmin < Real.log (1 / spec.η) := by
    rw [QLearningSpec.pmin_aux, div_lt_iff₀ hK] at hp
    rw [div_lt_iff₀ hp0]
    linarith
  have h₃ : Real.log (1 / spec.η) = -Real.log spec.η := by rw [one_div, Real.log_inv]
  calc _ = Real.exp (Real.log (Fintype.card (S × A)) * (1 / spec.pmin)) * Real.exp (Real.log spec.η) := by rw [Real.rpow_def_of_pos (by linarith), Real.exp_log h]
    _ = Real.exp (Real.log (Fintype.card (S × A)) * (1 / spec.pmin) + Real.log spec.η) := (Real.exp_add _ _).symm
    _ < Real.exp 0 := Real.exp_lt_exp.2 (by rw [mul_one_div]; linarith)
    _ = 1 := Real.exp_zero


-- created on 2026-09-26
