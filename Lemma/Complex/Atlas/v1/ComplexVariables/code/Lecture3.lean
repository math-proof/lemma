import Mathlib
import Initialize.Tactic.Attr.Basic
open Finset BigOperators Complex
open Complex
open scoped Polynomial ComplexConjugate


/--
[convexHull_finset_eq_convex_combinations](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture3.lean)
-/
@[path]
lemma convexHull_finset_eq_convex_combinations
  {S : Finset ℂ} :
-- imply
  (convexHull ℝ (↑S : Set ℂ)) = { x : ℂ | ∃ w : ℂ → ℝ, (∀ a ∈ S, 0 ≤ w a) ∧ ∑ a ∈ S, w a = 1 ∧ ∑ a ∈ S, w a • a = x } := by
-- proof
  ext x
  exact Finset.mem_convexHull'
open Complex
open scoped Polynomial ComplexConjugate

namespace Polynomial

/--
[gauss_lucas](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture3.lean)
-/
@[path]
lemma gauss_lucas
  {P : ℂ[X]}
-- given
  (hP : 0 < P.degree) :
-- imply
  P.derivative.rootSet ℂ ⊆ convexHull ℝ (P.rootSet ℂ) :=
-- proof
  rootSet_derivative_subset_convexHull_rootSet hP

end Polynomial


-- created on 2026-10-23
