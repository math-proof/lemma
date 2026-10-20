/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Galois/Infinite.lean -/

import Mathlib.FieldTheory.Galois.Infinite

/-!
# Topological closure of subgroups of an infinite Galois group

For an infinite Galois extension `K / k`, the topological closure (for the
Krull topology) of a subgroup `H` of `Gal(K/k)` is the fixing subgroup of its
fixed field.
-/

namespace InfiniteGalois

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The topological closure of a subgroup of an infinite Galois group is the
fixing subgroup of its fixed field. -/
theorem topologicalClosure_eq_fixingSubgroup_fixedField [IsGalois k K]
    (H : Subgroup Gal(K/k)) :
    H.topologicalClosure = (IntermediateField.fixedField H).fixingSubgroup := by
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
