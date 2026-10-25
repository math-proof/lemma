import Def.Analysis.MeasureTheory.Section_1_4_2.Part8
import Instance.Analysis.MeasureTheory.Section_1_4_3


/-- Example 1.4.25 (Restriction of a measure) -/
def FinitelyAdditiveMeasure.restrict {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) (A:Set X) (hA:B.measurable A) : FinitelyAdditiveMeasure (B.restrict A) :=
  {
    measure := fun E => μ.measure E
    measure_pos := fun E hE =>
      μ.measure_pos (Subtype.val '' E) ((B.restrict_iff hA E).mp hE)
    measure_empty := by
      simpa using μ.measure_empty
    measure_finite_additive := fun E F hE hF hdisj => by
      simpa [Set.image_union] using
        μ.measure_finite_additive (Subtype.val '' E) (Subtype.val '' F)
          ((B.restrict_iff hA E).mp hE) ((B.restrict_iff hA F).mp hF)
          (hdisj.image Subtype.val_injective.injOn (Set.subset_univ _) (Set.subset_univ _))
  }

/-- Example 1.4.26 (Counting a measure) -/
noncomputable def FinitelyAdditiveMeasure.counting (X:Type*) : FinitelyAdditiveMeasure (⊤  : ConcreteBooleanAlgebra X) :=
  {
    measure := fun E => ENat.card E
    measure_pos := fun _ _ => by positivity
    measure_empty := by simp
    measure_finite_additive := fun E F _ _ hdisj => by
      simp only [ENat.card_coe_set_eq, Set.encard_union_eq hdisj]
      norm_cast
  }

