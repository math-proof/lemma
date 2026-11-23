module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.EllipticCurves.code.Theorem161

public section

open Complex ComplexLattice


namespace ComplexTorus

/--
[proj_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexTorus.lean)
-/
public theorem proj_eq_iff
  {L : ComplexLattice}
  {z w : ℂ} :
-- imply
  proj L z = proj L w ↔ ∃ v ∈ L.toAddSubgroup, z + v = w :=
-- proof
  QuotientAddGroup.mk'_eq_mk' L.toAddSubgroup

end ComplexTorus


-- created on 2026-10-23
-- updated on 2026-11-23
