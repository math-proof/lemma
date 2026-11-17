module

public import Mathlib
public import Theorem.Analysis.Complex.Wiman.TaylorExpansion

public section

open Complex


namespace Complex

/--
[hasSum_wimanTaylorCoefficient_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/TaylorExpansion.lean)
-/
public theorem hasSum_wimanTaylorCoefficient_mul_pow
  {f : ℂ → ℂ}
  {z : ℂ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  HasSum (fun n : ℕ => wimanTaylorCoefficient f n * z ^ n) (f z) := by
-- proof
  simpa only [sub_zero, smul_eq_mul, wimanTaylorCoefficient, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using
    (Complex.hasSum_taylorSeries_of_entire hf 0 z)
end Complex



-- created on 2026-10-20
-- updated on 2026-10-26
