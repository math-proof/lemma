import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.PicardGroup
open TensorProduct InvertibleSheaves


namespace InvertibleSheaves

/--
[dual_tensor_self_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardGroup.lean)
-/
@[path]
lemma dual_tensor_self_equiv
  {R : Type u}
  [CommSemiring R]
  {M : Type*}
  [AddCommMonoid M]
  [Module R M]
  [Module.Invertible R M] :
-- imply
  Nonempty (Module.Dual R M ⊗[R] M ≃ₗ[R] R) :=
-- proof
  ⟨Module.Invertible.linearEquiv R M⟩

end InvertibleSheaves

namespace InvertibleSheaves

/--
[pic_mul_eq_tensor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardGroup.lean)
-/
@[path]
lemma pic_mul_eq_tensor
  {R : Type u}
  [CommSemiring R]
  [AddCommMonoid M]
  [Module R M]
  [Module.Invertible R M]
  [AddCommMonoid N]
  [Module R N]
  [Module.Invertible R N] :
-- imply
  CommRing.Pic.mk R (M ⊗[R] N) = CommRing.Pic.mk R M * CommRing.Pic.mk R N :=
-- proof
  CommRing.Pic.mk_tensor

end InvertibleSheaves

namespace InvertibleSheaves

/--
[pic_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardGroup.lean)
-/
@[path]
lemma pic_identity
  {R : Type u}
  [CommSemiring R] :
-- imply
  CommRing.Pic.mk R R = 1 :=
-- proof
  CommRing.Pic.mk_self

end InvertibleSheaves

namespace InvertibleSheaves

/--
[pic_inv_eq_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardGroup.lean)
-/
@[path]
lemma pic_inv_eq_dual
  {R : Type u}
  [CommSemiring R]
  [AddCommMonoid M]
  [Module R M]
  [Module.Invertible R M] :
-- imply
  CommRing.Pic.mk R (Module.Dual R M) = (CommRing.Pic.mk R M)⁻¹ :=
-- proof
  CommRing.Pic.mk_dual

end InvertibleSheaves

namespace InvertibleSheaves

/--
[pic_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardGroup.lean)
-/
@[path]
lemma pic_comm
  {R : Type u}
  [CommSemiring R]
  {a b : CommRing.Pic R} :
-- imply
  a * b = b * a :=
-- proof
  mul_comm a b

end InvertibleSheaves

namespace InvertibleSheaves

/--
[pic_eq_iff_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardGroup.lean)
-/
@[path]
lemma pic_eq_iff_iso
  {R : Type u}
  [CommSemiring R]
  [AddCommMonoid M]
  [Module R M]
  [Module.Invertible R M]
  [AddCommMonoid N]
  [Module R N]
  [Module.Invertible R N] :
-- imply
  CommRing.Pic.mk R M = CommRing.Pic.mk R N ↔ Nonempty (M ≃ₗ[R] N) :=
-- proof
  CommRing.Pic.mk_eq_mk_iff

end InvertibleSheaves

namespace InvertibleSheaves

/--
[pic_trivial_iff_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardGroup.lean)
-/
@[path]
lemma pic_trivial_iff_free
  {R : Type u}
  [CommSemiring R]
  [AddCommMonoid M]
  [Module R M]
  [Module.Invertible R M] :
-- imply
  CommRing.Pic.mk R M = 1 ↔ Module.Free R M :=
-- proof
  CommRing.Pic.mk_eq_one_iff_free

end InvertibleSheaves


-- created on 2026-10-23
