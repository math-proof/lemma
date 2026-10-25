import Def.Analysis.MeasureTheory.Section_1_4_2.Part8
import Theorem.Analysis.MeasureTheory.Section_1_4_3


/-- Example 1.4.21 (restriction to a subalgebra) -/
def FinitelyAdditiveMeasure.restrict_alg {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {B':ConcreteBooleanAlgebra X} (hBB': B' ≤ B) : FinitelyAdditiveMeasure B' :=
  {
    measure := μ.measure
    measure_pos := fun A hA => μ.measure_pos A (hBB' A hA)
    measure_empty := μ.measure_empty
    measure_finite_additive := fun E F hE hF hdisj =>
      μ.measure_finite_additive E F (hBB' E hE) (hBB' F hF) hdisj
  }

/-- Example 1.4.21 (Jordan measure) -/
noncomputable def FinitelyAdditiveMeasure.jordan (d:ℕ) : FinitelyAdditiveMeasure (JordanMeasurable.boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg (LebesgueMeasurable.gt_jordan_boolean_algebra d)

/-- Example 1.4.21 (null sets) -/
noncomputable def FinitelyAdditiveMeasure.null (d:ℕ) : FinitelyAdditiveMeasure (IsNull.boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg (IsNull.lt_lebesgue_boolean_algebra d)

/-- Example 1.4.21 (elementary sets) -/
noncomputable def FinitelyAdditiveMeasure.elem (d:ℕ) : FinitelyAdditiveMeasure (EuclideanSpace'.elementary_boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg
  (le_trans (JordanMeasurable.gt_elementary_boolean_algebra d)
    (LebesgueMeasurable.gt_jordan_boolean_algebra d))

open Classical in
/-- Example 1.4.22 (Dirac measure) -/
noncomputable def FinitelyAdditiveMeasure.dirac {X:Type*} (x₀:X) (B: ConcreteBooleanAlgebra X) : FinitelyAdditiveMeasure B :=
  {
    measure := fun A => if x₀ ∈ A then 1 else 0
    measure_pos := by
      intro A _
      split_ifs
      · exact zero_le_one
      · exact le_rfl
    measure_empty := by simp
    measure_finite_additive := by
      intro E F _ _ hdisj
      by_cases hxE : x₀ ∈ E
      · have hxF : x₀ ∉ F := fun hxF =>
          (Set.disjoint_left.mp hdisj hxE hxF)
        have hxU : x₀ ∈ E ∪ F := Or.inl hxE
        simp [hxE, hxF, hxU]
      · by_cases hxF : x₀ ∈ F
        · have hxU : x₀ ∈ E ∪ F := Or.inr hxF
          simp [hxE, hxF, hxU]
        · have hxU : x₀ ∉ E ∪ F := by simp [hxE, hxF]
          simp [hxE, hxF, hxU]
  }

