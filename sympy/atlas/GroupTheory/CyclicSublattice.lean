/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/CyclicSublattice.lean -/

import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Cyclic sublattices of additive commutative groups

This module introduces a reusable predicate recording when one additive
subgroup is a cyclic sublattice of another: the smaller subgroup is
contained in the larger one, and the quotient formed inside the larger
subgroup is cyclic.
-/

namespace AddSubgroup

variable {A : Type*} [AddCommGroup A]

/-- `L'` is a cyclic sublattice of `L` when `L'` is contained in `L` and
the quotient of `L` by (the restriction of) `L'` is cyclic. -/
def IsCyclicSublattice (L' L : AddSubgroup A) : Prop :=
  L' ≤ L ∧ IsAddCyclic (L ⧸ L'.addSubgroupOf L)

/-- Unfolding of `IsCyclicSublattice`. -/
theorem isCyclicSublattice_iff {L' L : AddSubgroup A} :
    IsCyclicSublattice L' L ↔
      L' ≤ L ∧ IsAddCyclic (L ⧸ L'.addSubgroupOf L) :=
  Iff.rfl

/-- A cyclic sublattice is contained in the ambient subgroup. -/
theorem IsCyclicSublattice.le {L' L : AddSubgroup A}
    (h : IsCyclicSublattice L' L) : L' ≤ L :=
  h.1

/-- The quotient witnessing cyclicity of a cyclic sublattice. -/
theorem IsCyclicSublattice.isAddCyclic_quotient {L' L : AddSubgroup A}
    (h : IsCyclicSublattice L' L) :
    IsAddCyclic (L ⧸ L'.addSubgroupOf L) :=
  h.2

/-- Constructor for `IsCyclicSublattice` from containment and cyclicity. -/
theorem IsCyclicSublattice.mk {L' L : AddSubgroup A} (hle : L' ≤ L)
    (hcyc : IsAddCyclic (L ⧸ L'.addSubgroupOf L)) :
    IsCyclicSublattice L' L :=
  ⟨hle, hcyc⟩

end AddSubgroup
