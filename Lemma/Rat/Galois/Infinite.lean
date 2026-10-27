import Mathlib
import Initialize.Tactic.Attr.Basic


namespace InfiniteGalois

/--
[topologicalClosure_eq_fixingSubgroup_fixedField](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Galois/Infinite.lean)
-/
@[path]
lemma topologicalClosure_eq_fixingSubgroup_fixedField
  [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {H : Subgroup Gal(K/k)} :
-- imply
  H.topologicalClosure = (IntermediateField.fixedField H).fixingSubgroup := by
-- proof
  apply le_antisymm
  · exact Subgroup.topologicalClosure_minimal H
    ((IntermediateField.le_iff_le _ _).mp le_rfl) (fixingSubgroup_isClosed _)
  · have hmono : H ≤ H.topologicalClosure := Subgroup.le_topologicalClosure H
    have hfix : IntermediateField.fixedField H.topologicalClosure ≤
      IntermediateField.fixedField H :=
      IntermediateField.fixedField_le hmono
    have hle : (IntermediateField.fixedField H).fixingSubgroup ≤
      (IntermediateField.fixedField H.topologicalClosure).fixingSubgroup :=
      IntermediateField.fixingSubgroup_le hfix
    rwa [fixingSubgroup_fixedField
      ⟨H.topologicalClosure, H.isClosed_topologicalClosure⟩] at hle

end InfiniteGalois


-- created on 2026-10-20
-- updated on 2026-10-26
