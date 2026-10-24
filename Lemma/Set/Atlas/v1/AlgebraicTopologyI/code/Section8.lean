import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section8
open ExactSequence AlgebraicTopologyI
open AlgebraicTopologyI


namespace ExactSequence

/--
[IntChainComplex.Subcomplex.quotientD_comp_quotientD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean)
-/
@[path]
lemma IntChainComplex.Subcomplex.quotientD_comp_quotientD
  [AddCommGroup A]
  [AddCommGroup B]
  [AddCommGroup C]
  {B : IntChainComplex}
  {A : B.Subcomplex}
  {n : ℤ} :
-- imply
  (A.quotientD B (n - 1)).comp (A.quotientD B n) = 0 := by
-- proof
  apply QuotientAddGroup.addMonoidHom_ext
  ext x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, quotientD,
    QuotientAddGroup.lift_mk', QuotientAddGroup.mk'_apply]
  have h := DFunLike.congr_fun (B.d_comp_d n) x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] at h
  simp [h]

end ExactSequence

namespace ExactSequence

/--
[IntChainComplex.Subcomplex.quotientComplex_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean)
-/
@[path]
lemma IntChainComplex.Subcomplex.quotientComplex_unique
  [AddCommGroup A]
  [AddCommGroup B]
  [AddCommGroup C]
  {B : IntChainComplex}
  {A : B.Subcomplex}
-- given
  (d' : ∀ n, B.X n ⧸ A.toSubgroup n →+ B.X (n - 1) ⧸ A.toSubgroup (n - 1))
  (hcomm : ∀ n, (d' n).comp (QuotientAddGroup.mk' (A.toSubgroup n)) = (QuotientAddGroup.mk' (A.toSubgroup (n - 1))).comp (B.d n)) :
-- imply
  ∀ n, d' n = A.quotientD B n := by
-- proof
  intro n
  have h_quot : (A.quotientD B n).comp (QuotientAddGroup.mk' (A.toSubgroup n)) =
    (QuotientAddGroup.mk' (A.toSubgroup (n - 1))).comp (B.d n) :=
    QuotientAddGroup.lift_comp_mk' _ _ _
  rw [← sub_eq_zero]
  apply QuotientAddGroup.addMonoidHom_ext
  ext x
  simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.zero_apply,
    QuotientAddGroup.mk'_apply, sub_eq_zero]
  have h1 := DFunLike.congr_fun (hcomm n) x
  have h2 := DFunLike.congr_fun h_quot x
  simp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply] at h1 h2
  rw [h1, h2]

end ExactSequence

namespace ExactSequence

/--
[IntChainComplex.d_castHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean)
-/
@[path]
lemma IntChainComplex.d_castHom
  [AddCommGroup A]
  [AddCommGroup B]
  [AddCommGroup C]
  {C : IntChainComplex}
  {m n : ℤ}
  {z : C.X m}
-- given
  (h : m = n) :
-- imply
  C.d n (C.castHom h z) = C.castHom (show m - 1 = n - 1 by omega) (C.d m z) := by
-- proof
  subst h; rfl

end ExactSequence

namespace AlgebraicTopologyI

/--
[NatChainComplex.Subcomplex.quotientD_comp_quotientD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean)
-/
@[path]
lemma NatChainComplex.Subcomplex.quotientD_comp_quotientD
  {B : NatChainComplex}
  {A : B.Subcomplex}
  {n : ℕ} :
-- imply
  (A.quotientD B n).comp (A.quotientD B (n + 1)) = 0 := by
-- proof
  apply QuotientAddGroup.addMonoidHom_ext
  ext x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply,
    QuotientAddGroup.mk'_apply]
  show (A.quotientD B n) ((A.quotientD B (n + 1)) (QuotientAddGroup.mk x)) = 0
  simp only [quotientD, QuotientAddGroup.lift_mk, AddMonoidHom.comp_apply,
    QuotientAddGroup.mk'_apply]
  have h := DFunLike.congr_fun (B.d_comp_d n) x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] at h
  simp [h]

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[relativeBoundaryMap_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean)
-/
@[path]
lemma relativeBoundaryMap_mk
  {n : ℕ}
  {X : Type*}
  [TopologicalSpace X]
  {A : Set X}
  {c : SingularChains (n + 1) X} :
-- imply
  relativeBoundaryMap n X A (QuotientAddGroup.mk c) = QuotientAddGroup.mk (boundaryMap n X c) := by
-- proof
  show QuotientAddGroup.lift _ _ _ (QuotientAddGroup.mk c) = _
  rw [QuotientAddGroup.lift_mk]
  rfl

end AlgebraicTopologyI

/--
[SingularSimplex.map_face](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean)
-/
@[path]
private lemma map_face_eq
  {n : ℕ}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  {f : C(X, Y)}
  {i : Fin (n + 2)}
  {σ : SingularSimplex (n + 1) X} :
-- imply
  SingularSimplex.face i (SingularSimplex.map f σ) = SingularSimplex.map f (SingularSimplex.face i σ) := by
-- proof
  apply AlgebraicTopologyI.SingularSimplex.map_face f i σ

/--
[SingularChains.map_comp_boundaryMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean)
-/
@[path]
private lemma map_comp_boundaryMap_eq
  {n : ℕ}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  {f : C(X, Y)} :
-- imply
  (boundaryMap n Y).comp (SingularChains.map f) = (SingularChains.map f).comp (boundaryMap n X) := by
-- proof
  apply AlgebraicTopologyI.SingularChains.map_comp_boundaryMap f

/--
[singularChainsInclusion_comm_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean)
-/
@[path]
private lemma singularChainsInclusion_comm_boundary_eq
  {n : ℕ}
  {X : Type*}
  [TopologicalSpace X]
  {A : Set X} :
-- imply
  (boundaryMap n X).comp (singularChainsInclusion (n + 1) X A) = (singularChainsInclusion n X A).comp (boundaryMap n ↥A) := by
-- proof
  apply AlgebraicTopologyI.singularChainsInclusion_comm_boundary n X A


-- created on 2026-10-23
