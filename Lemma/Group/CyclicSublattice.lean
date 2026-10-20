import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.CyclicSublattice
open AddSubgroup


/--
[isCyclicSublattice_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/CyclicSublattice.lean)
-/
@[path]
private lemma isCyclicSublattice_iff_eq
  [AddCommGroup A]
  {L' L : AddSubgroup A} :
-- imply
  IsCyclicSublattice L' L ↔
      L' ≤ L ∧ IsAddCyclic (L ⧸ L'.addSubgroupOf L) := by
-- proof
  apply AddSubgroup.isCyclicSublattice_iff

/--
[IsCyclicSublattice.le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/CyclicSublattice.lean)
-/
@[path]
private lemma IsCyclicSublattice_le_eq
  [AddCommGroup A]
  {L' L : AddSubgroup A}
-- given
  (h : IsCyclicSublattice L' L) :
-- imply
  L' ≤ L := by
-- proof
  apply AddSubgroup.IsCyclicSublattice.le h

/--
[IsCyclicSublattice.isAddCyclic_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/CyclicSublattice.lean)
-/
@[path]
private lemma IsCyclicSublattice_isAddCyclic_quotient_eq
  [AddCommGroup A]
  {L' L : AddSubgroup A}
-- given
  (h : IsCyclicSublattice L' L) :
-- imply
  IsAddCyclic (L ⧸ L'.addSubgroupOf L) := by
-- proof
  apply AddSubgroup.IsCyclicSublattice.isAddCyclic_quotient h

/--
[IsCyclicSublattice.mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/CyclicSublattice.lean)
-/
@[path]
private lemma IsCyclicSublattice_mk_eq
  [AddCommGroup A]
  {L' L : AddSubgroup A}
-- given
  (hle : L' ≤ L)
  (hcyc : IsAddCyclic (L ⧸ L'.addSubgroupOf L)) :
-- imply
  IsCyclicSublattice L' L := by
-- proof
  apply AddSubgroup.IsCyclicSublattice.mk hle hcyc


-- created on 2026-10-20
