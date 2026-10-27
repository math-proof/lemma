import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.GroupTheory.CyclicSublattice
open AddSubgroup


namespace AddSubgroup

/--
[isCyclicSublattice_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/CyclicSublattice.lean)
-/
@[path]
private lemma isCyclicSublattice_iff
  [AddCommGroup A]
  {L' L : AddSubgroup A} :
-- imply
  IsCyclicSublattice L' L ↔
      L' ≤ L ∧ IsAddCyclic (L ⧸ L'.addSubgroupOf L) :=
-- proof
  Iff.rfl

end AddSubgroup

namespace AddSubgroup

/--
[IsCyclicSublattice.le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/CyclicSublattice.lean)
-/
@[path]
private lemma IsCyclicSublattice.le
  [AddCommGroup A]
  {L' L : AddSubgroup A}
-- given
  (h : IsCyclicSublattice L' L) :
-- imply
  L' ≤ L :=
-- proof
  h.1

end AddSubgroup

namespace AddSubgroup

/--
[IsCyclicSublattice.isAddCyclic_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/CyclicSublattice.lean)
-/
@[path]
private lemma IsCyclicSublattice.isAddCyclic_quotient
  [AddCommGroup A]
  {L' L : AddSubgroup A}
-- given
  (h : IsCyclicSublattice L' L) :
-- imply
  IsAddCyclic (L ⧸ L'.addSubgroupOf L) :=
-- proof
  h.2

end AddSubgroup

namespace AddSubgroup

/--
[IsCyclicSublattice.mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/CyclicSublattice.lean)
-/
@[path]
private lemma IsCyclicSublattice.mk
  [AddCommGroup A]
  {L' L : AddSubgroup A}
-- given
  (hle : L' ≤ L)
  (hcyc : IsAddCyclic (L ⧸ L'.addSubgroupOf L)) :
-- imply
  IsCyclicSublattice L' L :=
-- proof
  ⟨hle, hcyc⟩

end AddSubgroup


-- created on 2026-10-20
-- updated on 2026-10-26
