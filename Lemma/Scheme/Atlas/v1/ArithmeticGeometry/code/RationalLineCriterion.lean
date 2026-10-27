import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
open ArithmeticGeometry


namespace ArithmeticGeometry

/--
[SmoothProjectiveCurve.exists_two_ratPoints](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RationalLineCriterion.lean)
-/
@[path]
lemma SmoothProjectiveCurve.exists_two_ratPoints
  [Field k]
  {C : SmoothProjectiveCurve k}
  [IsAlgClosed k] :
-- imply
  ∃ P Q : C.RatPoint, P ≠ Q :=
-- proof
  C.exists_two_ratPoints_of_algClosed ‹IsAlgClosed k›

end ArithmeticGeometry

namespace ArithmeticGeometry

/--
[SmoothProjectiveCurve.transcendental_of_principalDiv_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RationalLineCriterion.lean)
-/
@[path]
lemma SmoothProjectiveCurve.transcendental_of_principalDiv_ne_zero
  [Field k]
  {C : SmoothProjectiveCurve k}
  {f : C.FunField}
-- given
  (hf : C.principalDiv f ≠ 0) :
-- imply
  Transcendental k f := by
-- proof
  intro hfalg
  apply hf
  obtain ⟨a, ha⟩ := C.isAlgebraic_implies_mem_range_algebraMap f hfalg
  rw [← ha, C.principalDiv_algebraMap]

end ArithmeticGeometry

namespace ArithmeticGeometry

/--
[finrank_eq_one_of_subfield_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RationalLineCriterion.lean)
-/
@[path]
lemma finrank_eq_one_of_subfield_eq_top
  [Field k]
  [Field F]
  {K : Subfield F}
-- given
  (h : K = ⊤) :
-- imply
  Module.finrank K F = 1 := by
-- proof
  subst h
  have hbij : Function.Bijective (algebraMap (↥(⊤ : Subfield F)) F) :=
    ⟨Subtype.val_injective, fun x => ⟨⟨x, Subfield.mem_top x⟩, rfl⟩⟩
  have hle : LinearEquiv (RingHom.id ↥(⊤ : Subfield F)) ↥(⊤ : Subfield F) F :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) hbij
  rw [← hle.finrank_eq]
  exact Module.finrank_self _

end ArithmeticGeometry

namespace ArithmeticGeometry

/--
[exists_distinct_rational_points](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RationalLineCriterion.lean)
-/
@[path]
lemma exists_distinct_rational_points
  [Field k]
  [IsAlgClosed k]
  {C : SmoothProjectiveCurve k} :
-- imply
  ∃ P Q : C.RatPoint, P ≠ Q :=
-- proof
  C.exists_two_ratPoints

end ArithmeticGeometry

namespace ArithmeticGeometry

/--
[exists_injective_algHom_of_nontrivial_div](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RationalLineCriterion.lean)
-/
@[path]
lemma exists_injective_algHom_of_nontrivial_div
  [Field k]
  {C : SmoothProjectiveCurve k}
  {P Q : C.RatPoint}
  {f : C.FunField}
-- given
  (hPQ : P ≠ Q)
  (_hf : f ≠ 0)
  (hdiv : C.principalDiv f = C.pointToDivisor P + (- C.pointToDivisor Q)) :
-- imply
  ∃ φ : RatFunc k →ₐ[k] C.FunField, Function.Injective φ := by
-- proof
  have hdiv_ne : C.principalDiv f ≠ 0 := by
    rw [hdiv]
    intro h
    apply hPQ
    apply C.pointToDivisor_injective
    rwa [add_neg_eq_zero] at h
  have hf_trans : Transcendental k f := C.transcendental_of_principalDiv_ne_zero f hdiv_ne
  have hinj : Function.Injective (Polynomial.aeval (R := k) f) :=
    transcendental_iff_injective.mp hf_trans
  exact ⟨_, RatFunc.liftAlgHom_injective _ hinj⟩

end ArithmeticGeometry

namespace ArithmeticGeometry

/--
[iso_of_bijective_algHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RationalLineCriterion.lean)
-/
@[path]
lemma iso_of_bijective_algHom
  [Field k]
  {C : SmoothProjectiveCurve k}
  {φ : RatFunc k →ₐ[k] C.FunField}
-- given
  (hφ : Function.Bijective φ) :
-- imply
  C.IsIsomorphicToP1 :=
-- proof
  ⟨(AlgEquiv.ofBijective φ hφ).symm⟩

end ArithmeticGeometry

namespace ArithmeticGeometry

/--
[principal_of_Pic0_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RationalLineCriterion.lean)
-/
@[path]
lemma principal_of_Pic0_trivial
  [Field k]
  {C : SmoothProjectiveCurve k}
  {P Q : C.RatPoint}
-- given
  (htriv : C.Pic0IsTrivial) :
-- imply
  ∃ f : C.FunField, f ≠ 0 ∧ C.principalDiv f = C.pointToDivisor P + (- C.pointToDivisor Q) := by
-- proof
  have hdeg : C.degreeMap (C.pointToDivisor P + (-C.pointToDivisor Q)) = 0 := by
    rw [map_add, map_neg, C.degree_point P, C.degree_point Q]; omega
  have hcl : C.classMap (C.pointToDivisor P + (-C.pointToDivisor Q)) = 0 :=
    htriv _
  rwa [C.classMap_eq_zero_iff _ hdeg] at hcl
/-- Over an algebraically closed field, if $\operatorname{Pic}^0(C) = 0$ then $C \cong \mathbb{P}^1_k$. -/

end ArithmeticGeometry


-- created on 2026-10-23
