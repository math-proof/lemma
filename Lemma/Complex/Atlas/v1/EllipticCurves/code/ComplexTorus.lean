import Mathlib
import sympy.Basic
import Instance.v1.Atlas.EllipticCurves.code.ComplexTorus
open Complex ComplexLattice ComplexTorus


namespace ComplexTorus

/--
[proj_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexTorus.lean)
-/
@[path]
lemma proj_eq_iff
  {L : ComplexLattice}
  {z w : ℂ} :
-- imply
  proj L z = proj L w ↔ ∃ v ∈ L.toAddSubgroup, z + v = w :=
-- proof
  QuotientAddGroup.mk'_eq_mk' L.toAddSubgroup

end ComplexTorus


-- created on 2026-10-23
