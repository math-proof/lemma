import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.ProjectiveSpace
open ProjectiveSpace
open scoped LinearAlgebra.Projectivization


namespace ProjectiveSpace

/--
[coord_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ProjectiveSpace.lean)
-/
@[path]
lemma coord_ne_zero
  {n : ℕ}
  {k : Type*}
  [Field k]
  {P : Space n k} :
-- imply
  coord n k P ≠ 0 :=
-- proof
  Projectivization.rep_nonzero P

end ProjectiveSpace

namespace ProjectiveSpace

/--
[mk_eq_mk_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ProjectiveSpace.lean)
-/
@[path]
lemma mk_eq_mk_iff
  {n : ℕ}
  {k : Type*}
  [Field k]
  {v w : Fin (n + 1) → k}
-- given
  (hv : v ≠ 0)
  (hw : w ≠ 0) :
-- imply
  mk n k v hv = mk n k w hw ↔ ∃ a : kˣ, a • w = v :=
-- proof
  Projectivization.mk_eq_mk_iff k v w hv hw

end ProjectiveSpace

namespace ProjectiveSpace

/--
[mk_eq_mk_iff'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ProjectiveSpace.lean)
-/
@[path]
lemma mk_eq_mk_iff'
  {n : ℕ}
  {k : Type*}
  [Field k]
  {v w : Fin (n + 1) → k}
-- given
  (hv : v ≠ 0)
  (hw : w ≠ 0) :
-- imply
  mk n k v hv = mk n k w hw ↔ ∃ a : k, a • w = v :=
-- proof
  Projectivization.mk_eq_mk_iff' k v w hv hw

end ProjectiveSpace

namespace ProjectiveSpace

/--
[mk_coord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ProjectiveSpace.lean)
-/
@[path]
lemma mk_coord
  {n : ℕ}
  {k : Type*}
  [Field k]
  {v : Fin (n + 1) → k}
-- given
  (hv : v ≠ 0) :
-- imply
  Projectivization.mk k (coord n k (mk n k v hv)) (coord_ne_zero n k (mk n k v hv)) = mk n k v hv :=
-- proof
  Projectivization.mk_rep (mk n k v hv)
end ProjectiveSpace
namespace ProjectiveSpace

end ProjectiveSpace


-- created on 2026-10-23
