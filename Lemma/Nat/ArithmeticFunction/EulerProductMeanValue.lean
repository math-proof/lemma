import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.EulerProductMeanValue
open MetaMathlibExt


/--
[euler_product_mean_value](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/EulerProductMeanValue.lean)
-/
@[path]
private lemma euler_product_mean_value_eq
  {k : ℕ}
  {f : (Fin k → ℕ) → ℂ}
-- given
  (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) → f (fun i => a i * b i) = f a * f b)
  (hsumm : Summable (fun q : { q : { p : ℕ // p.Prime } × (Fin k → ℕ) // q.2 ≠ 0 } => ‖(∑ d ∈ Fintype.piFinset (fun i => Nat.divisors ((q.1.1 : ℕ) ^ (q.1.2 i))), (∏ i, ((ArithmeticFunction.moebius (d i) : ℤ) : ℂ)) * f (fun i => (q.1.1 : ℕ) ^ (q.1.2 i) / d i)) / (((q.1.1 : ℕ) : ℂ) ^ (∑ i, q.1.2 i))‖)) :
-- imply
  ∃ M : ℂ, Filter.Tendsto (fun N : ℕ =>
    (∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N), f n) / ((N : ℂ) ^ k))
    Filter.atTop (nhds M) ∧
    M = ∏' (p : { p : ℕ // p.Prime }),
    ((1 - 1 / ((p : ℕ) : ℂ)) ^ k *
    (∑' (ν : Fin k → ℕ),
    f (fun i => (p : ℕ) ^ (ν i)) / (((p : ℕ) : ℂ) ^ (∑ i, ν i)))) := by
-- proof
  apply MetaMathlibExt.euler_product_mean_value f hmult hsumm


-- created on 2026-10-20
