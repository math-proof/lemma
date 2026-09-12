import sympy.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory


@[main]
private lemma main
  {α : Type*}
  [MeasurableSpace α]
  {μ : Measure α}
  {f : α → ENNReal}
-- given
  (hf : Measurable f)
  (hμ : 0 < μ Set.univ)
  (h : ∀ᵐ x ∂μ, 0 < f x) :
-- imply
  0 < lintegral μ f := by
-- proof
  rw [lintegral_pos_iff_support hf]
  have hsup : μ (Function.support f) = μ Set.univ := by
    have heq : Function.support f =ᵐ[μ] (Set.univ : Set α) :=
      h.mono
        (q := fun x ↦ (x ∈ Function.support f) = (x ∈ (Set.univ : Set α)))
        fun _ hx ↦ by
          simp only [Function.mem_support, Set.mem_univ]
          exact eq_true hx.ne'
    exact heq.measure_eq
  rw [hsup]
  exact hμ


-- created on 2026-09-12
