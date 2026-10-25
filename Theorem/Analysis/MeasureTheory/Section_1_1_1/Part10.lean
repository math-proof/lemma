import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Instance.Analysis.MeasureTheory.Section_1_1_1.Part7
open BoundedInterval


/-- Coercing to {lean}`Box 1` is injective: equal boxes implies equal intervals. -/
@[simp]
theorem BoundedInterval.toBox_inj {I J: BoundedInterval} : (I:Box 1) = (J:Box 1) ↔ I = J := by
  refine' ⟨fun h => _, fun h => h ▸ rfl⟩
  have : (I:Box 1).side 0 = (J:Box 1).side 0 := by rw [h]
  exact this

/-- A 1D box's set equals the image of the interval under the {lean}`Real ≃ EuclideanSpace' 1` equivalence. -/
@[simp]
theorem BoundedInterval.coe_of_box (I:BoundedInterval) : (I:Box 1).toSet = Real.equiv_EuclideanSpace' '' I.toSet := by
  ext x; simp only [Box.mem_toSet, Set.mem_image]; constructor
  . intro h; use x 0; refine ⟨h 0, ?_⟩
    apply PiLp.ext; intro ⟨ i, hi ⟩; have : i=0 := by omega
    subst this; rfl
  rintro ⟨ y, hy, rfl ⟩ i
  have : i = 0 := Fin.ext_iff.mpr (by omega)
  subst this; exact hy

