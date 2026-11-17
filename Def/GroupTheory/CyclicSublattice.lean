/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/CyclicSublattice.lean -/

module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

@[expose] public section

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

end AddSubgroup
