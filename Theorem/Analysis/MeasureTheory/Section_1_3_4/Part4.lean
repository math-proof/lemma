import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
import Instance.Analysis.MeasureTheory.Section_1_3_4


-- Helper: integral of the zero simple function is zero
lemma UnsignedSimpleFunction.integ_zero {d:ℕ} :
    let h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
      use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
      exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
    h_simple.integ = 0 := by
  -- Use integral_eq with k=0 to compute the integral
  have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
    use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
    exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
  have heq : (0 : EuclideanSpace' d → EReal) = ∑ i : Fin 0, ((Fin.elim0 i : EReal) • (EReal.indicator (Fin.elim0 i : Set (EuclideanSpace' d)))) := by
    funext x; simp [Finset.univ_eq_empty]
  have hmes : ∀ i : Fin 0, LebesgueMeasurable (Fin.elim0 i : Set (EuclideanSpace' d)) := fun i => Fin.elim0 i
  have hnonneg : ∀ i : Fin 0, (Fin.elim0 i : EReal) ≥ 0 := fun i => Fin.elim0 i
  have h_integ := UnsignedSimpleFunction.integral_eq h_simple hmes hnonneg heq
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at h_integ
  exact h_integ

-- Helper: integral of unsigned measurable function is nonnegative
lemma UnsignedLebesgueIntegral.nonneg {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) :
    0 ≤ UnsignedLebesgueIntegral f := by
  simp only [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
  apply le_csSup_of_le ⟨⊤, fun _ _ => le_top⟩ _ (le_refl 0)
  use 0
  have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
    use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
    exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
  use h_simple; intro x
  constructor
  · simp only [Pi.zero_apply]; exact hf.1 x
  · have : h_simple.integ = 0 := UnsignedSimpleFunction.integ_zero
    rw [this]

