/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/PowerSeries/BinomialTransformGeneratingFunction.lean -/


import Lemma.Int.PowerSeries.BinomialTransformGeneratingFunction
import Mathlib.Algebra.Field.ZMod


namespace MetaMathlibExt

example (a : ℕ → ZMod 2) :
    PowerSeries.mk
        (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 2) * a k) =
      (1 - (PowerSeries.X : PowerSeries (ZMod 2)))⁻¹ *
        (PowerSeries.mk a).subst
          ((PowerSeries.X : PowerSeries (ZMod 2)) * (1 - PowerSeries.X)⁻¹) :=
  mk_sum_choose_mul_eq_inv_one_sub_mul_subst a

example (a : ℕ → ℚ) :
    PowerSeries.mk (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * a k) =
      (1 - PowerSeries.X)⁻¹ * (PowerSeries.mk a).subst (PowerSeries.X * (1 - PowerSeries.X)⁻¹) :=
  mk_sum_choose_mul_eq_inv_one_sub_mul_subst _

example (a : ℕ → ℝ) :
    PowerSeries.mk (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a k) =
      (1 - PowerSeries.X)⁻¹ * (PowerSeries.mk a).subst (PowerSeries.X * (1 - PowerSeries.X)⁻¹) :=
  ordinary_generating_function_binomial_transform a

end MetaMathlibExt
