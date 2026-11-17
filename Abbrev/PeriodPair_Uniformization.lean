module

public import Mathlib

set_option autoImplicit false

@[expose] public noncomputable section

open scoped PeriodPair UpperHalfPlane

namespace PeriodPair

variable (L : PeriodPair)

section Scale

variable (α : ℂˣ)

end Scale

abbrev sublatticeQuotient (L L' : PeriodPair) :=
  L.lattice.toAddSubgroup ⧸ L'.lattice.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup

end PeriodPair

end
