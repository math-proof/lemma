import Mathlib
import sympy.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.EllipticRegularityConcrete.Part2
open EllipticRegularityConcrete


namespace EllipticRegularityConcrete

/--
[isSmoothForm_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticRegularityConcrete.lean)
-/
@[path]
lemma isSmoothForm_sub
  {n k : ℕ}
  {a b : DiffForm n k}
-- given
  (ha : IsSmoothForm a)
  (hb : IsSmoothForm b) :
-- imply
  IsSmoothForm (a - b) :=
-- proof
  ha.sub hb

end EllipticRegularityConcrete


-- created on 2026-10-23
