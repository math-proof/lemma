import Mathlib
import sympy.Basic
import sympy.calculus.ode.MaximalSolution

open Set

/--
[MaximalSolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/MaximalSolution.lean)
-/
@[path]
private lemma has_deriv_at_piecewise_union_of_eq_on_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ℝ → E → E} {x y : ℝ → E} {I J : Set ℝ}
  (hI : IsOpen I)
  (hJ : IsOpen J)
  (hx : ∀ t ∈ I, HasDerivAt x (v t (x t)) t)
  (hy : ∀ t ∈ J, HasDerivAt y (v t (y t)) t)
  (hxy : EqOn x y (I ∩ J)) :
-- imply
  ∃ z : ℝ → E, EqOn z x I ∧ EqOn z y J ∧ ∀ t ∈ I ∪ J, HasDerivAt z (v t (z t)) t := by
-- proof
  apply hasDerivAt_piecewise_union_of_eqOn hI hJ hx hy hxy

/--
[MaximalSolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/MaximalSolution.lean)
-/
@[path]
private lemma ode_global_exists_of_global_lipschitz_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (f : ℝ → E → E)
  (L : NNReal)
  (hfcont : Continuous (Function.uncurry f))
  (hlip : ∀ t, LipschitzWith L (f t))
  (t₀ : ℝ)
  (x₀ : E) :
-- imply
  ∃! x : ℝ → E, x t₀ = x₀ ∧ ∀ t, HasDerivAt x (f t (x t)) t := by
-- proof
  apply ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz f t₀ x₀ L hfcont hlip

/--
[MaximalSolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/MaximalSolution.lean)
-/
@[path]
private lemma ode_maximal_solution_exit_compact_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (U : Set (ℝ × E))
  (f : ℝ × E → E)
  (t₀ : ℝ)
  (x₀ : E)
  (hU : IsOpen U)
  (hmem : (t₀, x₀) ∈ U)
  (hf : ContinuousOn f U)
  (hlip : ∀ p ∈ U, ∃ C : NNReal, ∃ s ∈ nhds p,
    ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ U → (t, y) ∈ s ∩ U →
      dist (f (t, x)) (f (t, y)) ≤ C * dist x y) :
-- imply
  ∃ I : Set ℝ, ∃ x : ℝ → E, x t₀ = x₀ ∧ IsOpen I ∧ t₀ ∈ I ∧
    (∀ t₁ ∈ I, ∀ t₂ ∈ I, Set.Icc t₁ t₂ ⊆ I) ∧
    (∀ t ∈ I, (t, x t) ∈ U ∧ HasDerivAt x (f (t, x t)) t) ∧
    ∀ K : Set (ℝ × E), IsCompact K → K ⊆ U →
      (∃ c ∈ I, ∀ t ∈ I, c ≤ t → (t, x t) ∉ K) ∧
      ∃ c ∈ I, ∀ t ∈ I, t ≤ c → (t, x t) ∉ K := by
-- proof
  apply ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact U f t₀ x₀ hU hmem hf hlip

-- created on 2026-10-10
