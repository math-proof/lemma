import Mathlib
import sympy.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.ProjectiveSpaceDef
open ProjectiveSpace
open scoped LinearAlgebra.Projectivization


namespace ProjectiveSpace

/--
[mk_eq_mk_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveSpaceDef.lean)
-/
@[path]
lemma mk_eq_mk_iff
  [DivisionRing k]
  {n : ℕ}
  {v w : Fin (n + 1) → k}
-- given
  (hv : v ≠ 0)
  (hw : w ≠ 0) :
-- imply
  mk v hv = mk w hw ↔ ∃ a : kˣ, a • w = v :=
-- proof
  Projectivization.mk_eq_mk_iff k v w hv hw

end ProjectiveSpace

namespace ProjectiveSpace

/--
[mk_eq_mk_iff'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveSpaceDef.lean)
-/
@[path]
lemma mk_eq_mk_iff'
  [DivisionRing k]
  {n : ℕ}
  {v w : Fin (n + 1) → k}
-- given
  (hv : v ≠ 0)
  (hw : w ≠ 0) :
-- imply
  mk v hv = mk w hw ↔ ∃ a : k, a • w = v :=
-- proof
  Projectivization.mk_eq_mk_iff' k v w hv hw

end ProjectiveSpace

namespace ProjectiveSpace

/--
[quotientMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveSpaceDef.lean)
-/
@[path]
lemma quotientMap_surjective
  [DivisionRing k]
  {n : ℕ} :
-- imply
  Function.Surjective (quotientMap (k := k) (n := n)) :=
-- proof
  Quotient.mk''_surjective

end ProjectiveSpace

namespace ProjectiveSpace

/--
[rep_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveSpaceDef.lean)
-/
@[path]
lemma rep_nonzero
  [DivisionRing k]
  {n : ℕ}
  {p : ProjectiveSpace k n} :
-- imply
  rep p ≠ 0 :=
-- proof
  Projectivization.rep_nonzero p

end ProjectiveSpace

namespace ProjectiveSpace

/--
[mk_rep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveSpaceDef.lean)
-/
@[path]
lemma mk_rep
  [DivisionRing k]
  {n : ℕ}
  {p : ProjectiveSpace k n} :
-- imply
  mk (rep p) (rep_nonzero p) = p :=
-- proof
  Projectivization.mk_rep p

end ProjectiveSpace


-- created on 2026-10-23
