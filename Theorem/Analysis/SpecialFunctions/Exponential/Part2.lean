import Lemma.Hyperreal.UFn.of.All_UFn
import Lemma.Int.Abs.eq.Max_Neg
import Def.Analysis.SpecialFunctions.Exponential.Part2
open Filter Hyperreal Int


theorem Hyperreal.exp_neg x : exp (-x) = (exp x)⁻¹ := by
  apply UFn.of.All_UFn x
  intro x
  apply Germ.coe_eq.mpr ∘ Eventually.of_forall
  simp [Real.exp_neg]

theorem Hyperreal.exp_ne_zero x : exp x ≠ 0 := by
  apply UFn.of.All_UFn x
  intro x h
  obtain ⟨n, hn⟩ := nonempty_of_mem (Germ.coe_eq.mp h)
  simp at hn

theorem Hyperreal.exp_pos x : exp x > 0 := by
  apply UFn.of.All_UFn x
  intro x
  apply Germ.coe_lt.mpr ∘ Eventually.of_forall
  simp [Real.exp_pos]

-- copied from Mathlib\Analysis\Complex\Exponential.lean
theorem Real.add_one_lt_exp_of_pos {x : ℝ} (hx : 0 < x) : x + 1 < exp x :=
  (by nlinarith : x + 1 < 1 + x + x ^ 2 / 2).trans_le (quadratic_le_exp_of_nonneg hx.le)

-- copied from Mathlib\Analysis\Complex\Exponential.lean
theorem Real.add_one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x + 1 ≤ exp x := by
  obtain rfl | h := eq_or_lt_of_le hx
  · simp
  exact (add_one_lt_exp_of_pos h).le

theorem Hyperreal.add_one_le_exp_of_nonneg (hx : 0 ≤ x) : x + 1 ≤ exp x := by
  revert hx
  apply UFn.of.All_UFn x
  intro x hx
  apply Germ.coe_le.mpr
  filter_upwards [Germ.coe_nonneg.mp hx] with _ hn
  exact Real.add_one_le_exp_of_nonneg hn

@[mono, gcongr]
theorem Hyperreal.exp_strictMono : StrictMono exp := fun x y h => by
  rw [← sub_add_cancel y x, exp_add]
  exact (lt_mul_iff_one_lt_left (exp_pos _)).2 (lt_of_lt_of_le (by linarith) (add_one_le_exp_of_nonneg (by linarith)))

theorem Hyperreal.exp_injective : Function.Injective Hyperreal.exp :=
  exp_strictMono.injective

theorem Hyperreal.exp_eq_exp : exp x = exp y ↔ x = y :=
  exp_injective.eq_iff

