import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceDerivative.booleanFourier.influence_filter_card_eq
open BooleanFourier Bool


/--
[influence_eq_l2_norm_sq_discreteDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InfluenceDerivative.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {f : (Fin (n + 1) → Bool) → Bool}
  {i : Fin (n + 1)} :
-- imply
  influence f i = (∑ y : Fin n → Bool, boolDiscreteDerivative (fun x => boolToSign (f x)) i y ^ 2) / (2 ^ n : ℝ) := by
-- proof
  have deriv_sq : ∀ y : Fin n → Bool,
    boolDiscreteDerivative (fun x => boolToSign (f x)) i y ^ 2 =
    if f (Fin.insertNth i true y) = f (Fin.insertNth i false y) then (0 : ℝ) else 1 := by
    intro y
    simp only [boolDiscreteDerivative, boolToSign]
    cases f (Fin.insertNth i true y) <;> cases f (Fin.insertNth i false y) <;> simp <;> norm_num
  simp_rw [deriv_sq]
  rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, zero_add, nsmul_eq_mul, mul_one]
  simp only [influence]
  rw [influence_filter_card_eq]
  push_cast
  rw [pow_succ]
  ring


lemma BooleanFourier.influence_eq_l2_norm_sq_discreteDerivative
  {n : ℕ}
  {f : (Fin (n + 1) → Bool) → Bool}
  {i : Fin (n + 1)} :
-- imply
  influence f i = (∑ y : Fin n → Bool, boolDiscreteDerivative (fun x => boolToSign (f x)) i y ^ 2) / (2 ^ n : ℝ) := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
