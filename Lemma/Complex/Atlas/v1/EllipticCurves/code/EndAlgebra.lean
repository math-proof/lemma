import Mathlib
import sympy.Basic
import Instance.v1.Atlas.EllipticCurves.code.EndAlgebra.Part5
open RingAntiHom RingInvolution
open scoped TensorProduct


namespace RingAntiHom

/--
[coe_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndAlgebra.lean)
-/
@[path]
lemma coe_mk
  [Ring R]
  [Ring S]
  {f : R → S}
  (hadd hone hmul) :
-- imply
  ⇑(RingAntiHom.mk f hadd hone hmul) = f :=
-- proof
  rfl

end RingAntiHom

namespace RingInvolution

/--
[map_mul_rev'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndAlgebra.lean)
-/
@[path]
lemma map_mul_rev'
  [Ring R]
  {φ : RingInvolution R}
  {a b : R} :
-- imply
  φ (a * b) = φ b * φ a :=
-- proof
  φ.toRingAntiHom.map_mul_rev a b

end RingInvolution

namespace RingInvolution

/--
[map_one'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndAlgebra.lean)
-/
@[path]
lemma map_one'
  [Ring R]
  {φ : RingInvolution R} :
-- imply
  φ 1 = 1 :=
-- proof
  φ.toRingAntiHom.map_one

end RingInvolution

namespace RingInvolution

/--
[map_add'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndAlgebra.lean)
-/
@[path]
lemma map_add'
  [Ring R]
  {φ : RingInvolution R}
  {a b : R} :
-- imply
  φ (a + b) = φ a + φ b :=
-- proof
  φ.toRingAntiHom.map_add a b

end RingInvolution

namespace RingInvolution

/--
[bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndAlgebra.lean)
-/
@[path]
lemma bijective
  [Ring R]
  {φ : RingInvolution R} :
-- imply
  Function.Bijective φ.toFun :=
-- proof
  ⟨fun a b h => by rw [← φ.involution a, ← φ.involution b, h],
    fun b => ⟨φ b, φ.involution b⟩⟩

end RingInvolution


-- created on 2026-10-23
