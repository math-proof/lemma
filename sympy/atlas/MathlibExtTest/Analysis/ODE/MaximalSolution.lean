/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/ODE/MaximalSolution.lean -/


import sympy.atlas.Analysis.ODE.MaximalSolution
import Lemma.Set.Any_And_EqOnAndAll_HasDerivAt.of.EqOn_Inter.All_HasDerivAt.All_HasDerivAt.IsOpen.IsOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Filter Set
open MathlibExt.Analysis.ODE.MaximalSolutionWanted

-- Global uniqueness identifies the exponential solution.
example :
    ∃ x : ℝ → ℝ, x 0 = 1 ∧ x 1 = Real.exp 1 ∧ ∀ t, HasDerivAt x (x t) t := by
  have hcont : Continuous (Function.uncurry (fun (_ : ℝ) (x : ℝ) ↦ x)) := by
    fun_prop
  have hlip : ∀ t : ℝ, LipschitzWith (1 : NNReal) (fun x : ℝ ↦ x) :=
    fun _ ↦ LipschitzWith.id
  obtain ⟨x, hx, hunique⟩ := ode_global_exists_of_global_lipschitz
    (fun (_ : ℝ) (x : ℝ) ↦ x) 0 1 1 hcont hlip
  have hexp : Real.exp 0 = 1 ∧ ∀ t, HasDerivAt Real.exp (Real.exp t) t :=
    ⟨Real.exp_zero, Real.hasDerivAt_exp⟩
  have hexp_eq : Real.exp = x := hunique Real.exp hexp
  exact ⟨x, hx.1, by rw [← hexp_eq], hx.2⟩

-- Clipped local solutions of x' = 1 glue to the identity on the whole line.
example :
    ∃ z : ℝ → ℝ, (∀ t, z t = t) ∧ ∀ t, HasDerivAt z 1 t := by
  obtain ⟨z, hzleft, hzright, hzderiv⟩ := hasDerivAt_piecewise_union_of_eqOn
    (v := fun (_ : ℝ) (_ : ℝ) ↦ 1) (x := fun t : ℝ ↦ min t 1)
    (y := fun t : ℝ ↦ max t (-1)) (I := Iio 1) (J := Ioi (-1))
    isOpen_Iio isOpen_Ioi
    (fun t ht ↦ by
      have heq : (fun u : ℝ ↦ min u 1) =ᶠ[nhds t] id := by
        filter_upwards [Iio_mem_nhds ht] with u hu
        simp only [min_eq_left hu.le, id_eq]
      exact (hasDerivAt_id t).congr_of_eventuallyEq heq)
    (fun t ht ↦ by
      have heq : (fun u : ℝ ↦ max u (-1)) =ᶠ[nhds t] id := by
        filter_upwards [Ioi_mem_nhds ht] with u hu
        simp only [max_eq_left hu.le, id_eq]
      exact (hasDerivAt_id t).congr_of_eventuallyEq heq)
    (fun t ht ↦ by
      change min t 1 = max t (-1)
      rw [min_eq_left ht.1.le, max_eq_left ht.2.le])
  have hcover : ∀ t : ℝ, t ∈ Iio 1 ∪ Ioi (-1) := by
    intro t
    by_cases ht : t < 1
    · exact Or.inl ht
    · exact Or.inr (lt_of_lt_of_le (by norm_num) (le_of_not_gt ht))
  refine ⟨z, ?_, fun t ↦ hzderiv t (hcover t)⟩
  intro t
  rcases hcover t with ht | ht
  · simpa only [min_eq_left ht.le] using hzleft ht
  · simpa only [max_eq_left ht.le] using hzright ht

-- The zero field has a maximal interval whose graph exits a compact square at both ends.
example :
    ∃ I : Set ℝ, ∃ x : ℝ → ℝ, 0 ∈ I ∧ x 0 = 0 ∧
      (∀ t ∈ I, HasDerivAt x 0 t) ∧
      (∃ c ∈ I, ∀ t ∈ I, c ≤ t →
        (t, x t) ∉ (Icc (-1) 1 ×ˢ Icc (-1) 1)) ∧
      ∃ c ∈ I, ∀ t ∈ I, t ≤ c →
        (t, x t) ∉ (Icc (-1) 1 ×ˢ Icc (-1) 1) := by
  have hlip : ∀ p ∈ (Set.univ : Set (ℝ × ℝ)), ∃ C : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : ℝ, (t, x) ∈ s ∩ Set.univ → (t, y) ∈ s ∩ Set.univ →
        dist (0 : ℝ) 0 ≤ C * dist x y := by
    intro p _
    refine ⟨0, Set.univ, univ_mem, ?_⟩
    simp
  obtain ⟨I, x, hx₀, _, ht₀, _, hx, hexit⟩ := ode_maximal_solution_exit_compact
    (Set.univ : Set (ℝ × ℝ)) (fun _ ↦ 0) 0 0 isOpen_univ trivial
      continuousOn_const hlip
  obtain ⟨hright, hleft⟩ := hexit (Icc (-1) 1 ×ˢ Icc (-1) 1)
    (isCompact_Icc.prod isCompact_Icc) (by simp)
  refine ⟨I, x, ht₀, hx₀, fun t ht ↦ (hx t ht).2, ?_, ?_⟩
  · exact hright
  · exact hleft
