import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingReflectionKernel
open Finset Filter StatMech StatMech.FrontierA


/--
[dotProduct_pow_kernel_quadratic_eq_squares](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingReflectionKernel.lean)
-/
@[path]
private lemma dotProduct_pow_kernel_quadratic_eq_squares_eq
  [Fintype I]
  [Fintype C]
  {u : I → C → Real}
  {a : I → Real}
  {n : Nat} :
-- imply
  (∑ i : I, ∑ j : I, a i * a j * (∑ c : C, u i c * u j c) ^ n) = ∑ p : Fin n → C, (∑ i : I, a i * ∏ r : Fin n, u i (p r)) ^ 2 := by
-- proof
  apply StatMech.FrontierA.dotProduct_pow_kernel_quadratic_eq_squares u a n

/--
[dotProduct_pow_kernel_quadratic_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingReflectionKernel.lean)
-/
@[path]
private lemma dotProduct_pow_kernel_quadratic_nonneg_eq
  [Fintype I]
  [Fintype C]
  {u : I → C → Real}
  {a : I → Real}
  {n : Nat} :
-- imply
  0 ≤ ∑ i : I, ∑ j : I, a i * a j * (∑ c : C, u i c * u j c) ^ n := by
-- proof
  apply StatMech.FrontierA.dotProduct_pow_kernel_quadratic_nonneg u a n

/--
[exp_dotProduct_kernel_quadratic_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingReflectionKernel.lean)
-/
@[path]
private lemma exp_dotProduct_kernel_quadratic_nonneg_eq
  [Fintype I]
  [Fintype C]
  {beta : Real}
  {u : I → C → Real}
  {a : I → Real}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  0 ≤ ∑ i : I, ∑ j : I, a i * a j * Real.exp (beta * ∑ c : C, u i c * u j c) := by
-- proof
  apply StatMech.FrontierA.exp_dotProduct_kernel_quadratic_nonneg beta hbeta u a

/--
[exp_dotProduct_kernel_reflection_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingReflectionKernel.lean)
-/
@[path]
private lemma exp_dotProduct_kernel_reflection_inequality_eq
  [Fintype I]
  [Fintype C]
  {beta : Real}
  {u : I → C → Real}
  {A B : I → Real}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  2 * (∑ i : I, ∑ j : I, A i * B j * Real.exp (beta * ∑ c : C, u i c * u j c)) ≤ (∑ i : I, ∑ j : I, A i * A j * Real.exp (beta * ∑ c : C, u i c * u j c)) + ∑ i : I, ∑ j : I, B i * B j * Real.exp (beta * ∑ c : C, u i c * u j c) := by
-- proof
  apply StatMech.FrontierA.exp_dotProduct_kernel_reflection_inequality beta hbeta u A B

/--
[exp_dotProduct_two_family_reflection_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingReflectionKernel.lean)
-/
@[path]
private lemma exp_dotProduct_two_family_reflection_inequality_eq
  [Fintype I]
  [Fintype C]
  {beta : Real}
  {u v : I → C → Real}
  {A B : I → Real}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  2 * (∑ i : I, ∑ j : I, A i * B j * Real.exp (beta * ∑ c : C, u i c * v j c)) ≤ (∑ i : I, ∑ j : I, A i * A j * Real.exp (beta * ∑ c : C, u i c * u j c)) + ∑ i : I, ∑ j : I, B i * B j * Real.exp (beta * ∑ c : C, v i c * v j c) := by
-- proof
  apply StatMech.FrontierA.exp_dotProduct_two_family_reflection_inequality beta hbeta u v A B


-- created on 2026-10-23
