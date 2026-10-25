import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.IsogenyKernelAut.Part2
open WeierstrassCurve EllipticCurveIsogeny EllipticCurveIsogeny.KernelAutData EllipticCurveIsogeny.TranslationPullbackData


namespace EllipticCurveIsogeny

/--
[hom_invariant_under_ker_translation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean)
-/
@[path]
lemma hom_invariant_under_ker_translation
  [Field F]
  [DecidableEq F]
  {W₁ W₂ : WeierstrassCurve F}
  [W₁.IsElliptic]
  [W₂.IsElliptic]
  {φ_hom : W₁.toAffine.Point →+ W₂.toAffine.Point}
  {P : W₁.toAffine.Point}
-- given
  (hP : P ∈ φ_hom.ker) :
-- imply
  ∀ R : W₁.toAffine.Point, φ_hom (R + P) = φ_hom R := by
-- proof
  intro R
  rw [map_add]
  have : φ_hom P = 0 := hP
  rw [this, add_zero]
namespace KernelAutData
variable {F : Type*} [Field F] [DecidableEq F]
  {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
  {φ_hom : W₁.toAffine.Point →+ W₂.toAffine.Point}
  (data : KernelAutData φ_hom)

end EllipticCurveIsogeny

namespace EllipticCurveIsogeny.KernelAutData

/--
[comp_translation_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean)
-/
@[path]
lemma comp_translation_ker
  [Field F]
  [DecidableEq F] :
-- imply
  ∀ (P : W₁.toAffine.Point), P ∈ φ_hom.ker → ∀ (x : data.PullbackField), (data.translationPullback P) (algebraMap data.PullbackField data.FunctionField x) = algebraMap data.PullbackField data.FunctionField x := by
-- proof
  intro P hP x
  apply data.eval_ext
  intro Q
  rw [data.eval_translationPullback]
  exact data.eval_algebraMap_eq_of_image_eq x (Q + P) Q
    (hom_invariant_under_ker_translation φ_hom P hP Q)

end EllipticCurveIsogeny.KernelAutData

namespace EllipticCurveIsogeny.KernelAutData

/--
[translation_comp_pullback](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean)
-/
@[path]
lemma translation_comp_pullback
  [Field F]
  [DecidableEq F] :
-- imply
  ∀ (P Q : W₁.toAffine.Point), data.translationPullback (P + Q) = (data.translationPullback P) * (data.translationPullback Q) := by
-- proof
  intro P Q
  ext f : 1
  apply data.eval_ext
  intro R
  rw [data.eval_translationPullback]
  show data.eval f (R + (P + Q)) =
    data.eval (((data.translationPullback P) * (data.translationPullback Q)) f) R
  simp only [RingAut.mul_apply]
  rw [data.eval_translationPullback P (data.translationPullback Q f) R]
  rw [data.eval_translationPullback Q f (R + P)]
  rw [← add_assoc]

end EllipticCurveIsogeny.KernelAutData

namespace EllipticCurveIsogeny.KernelAutData

/--
[nontrivial_translation_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean)
-/
@[path]
lemma nontrivial_translation_nontrivial
  [Field F]
  [DecidableEq F] :
-- imply
  ∀ (P : W₁.toAffine.Point), P ≠ 0 → data.translationPullback P ≠ 1 := by
-- proof
  intro P hP h_eq
  have h_eval : ∀ f Q, data.eval f (Q + P) = data.eval f Q := by
    intro f Q
    have := data.eval_translationPullback P f Q
    rw [h_eq] at this
    simp only [RingAut.one_apply] at this
    exact this.symm
  have h_zero : ∀ f, data.eval f P = data.eval f 0 := by
    intro f
    have := h_eval f 0
    rwa [zero_add] at this
  obtain ⟨f, hf⟩ := data.eval_separates P 0 hP
  exact hf (h_zero f)

end EllipticCurveIsogeny.KernelAutData

namespace EllipticCurveIsogeny.KernelAutData

/--
[translationPullback_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean)
-/
@[path]
lemma translationPullback_zero
  [Field F]
  [DecidableEq F] :
-- imply
  data.translationPullback 0 = 1 := by
-- proof
  have h := data.translation_comp_pullback 0 0
  simp only [add_zero] at h
  set a := data.translationPullback 0
  have : a⁻¹ * a = a⁻¹ * (a * a) := congrArg (a⁻¹ * ·) h
  simp only [inv_mul_cancel, inv_mul_cancel_left] at this
  exact this.symm

end EllipticCurveIsogeny.KernelAutData

namespace EllipticCurveIsogeny.KernelAutData

/--
[translationPullback_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean)
-/
@[path]
lemma translationPullback_neg
  [Field F]
  [DecidableEq F]
  {P : W₁.toAffine.Point} :
-- imply
  data.translationPullback (-P) = (data.translationPullback P)⁻¹ := by
-- proof
  have h := data.translation_comp_pullback P (-P)
  simp only [add_neg_cancel] at h
  rw [data.translationPullback_zero] at h
  exact mul_left_cancel (h.symm.trans (mul_inv_cancel _).symm)

end EllipticCurveIsogeny.KernelAutData

namespace EllipticCurveIsogeny.KernelAutData

/--
[translationPullback_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean)
-/
@[path]
lemma translationPullback_sub
  [Field F]
  [DecidableEq F]
  {P Q : W₁.toAffine.Point} :
-- imply
  data.translationPullback (P - Q) = (data.translationPullback P) * (data.translationPullback Q)⁻¹ := by
-- proof
  rw [sub_eq_add_neg, data.translation_comp_pullback, data.translationPullback_neg]

end EllipticCurveIsogeny.KernelAutData

namespace EllipticCurveIsogeny.KernelAutData

/--
[translationPullback_fixes_image](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean)
-/
@[path]
lemma translationPullback_fixes_image
  [Field F]
  [DecidableEq F]
  {P : W₁.toAffine.Point}
  {x : data.PullbackField}
-- given
  (hP : P ∈ φ_hom.ker) :
-- imply
  (data.translationPullback P) (algebraMap data.PullbackField data.FunctionField x) = algebraMap data.PullbackField data.FunctionField x :=
-- proof
  data.comp_translation_ker P hP x

end EllipticCurveIsogeny.KernelAutData

namespace EllipticCurveIsogeny.KernelAutData

/--
[translationPullback_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean)
-/
@[path]
lemma translationPullback_injective
  [Field F]
  [DecidableEq F] :
-- imply
  Function.Injective data.translationPullback := by
-- proof
  intro P Q h
  suffices P - Q = 0 by exact sub_eq_zero.mp this
  have h_sub : data.translationPullback (P - Q) = 1 := by
    rw [data.translationPullback_sub]
    rw [h]
    exact mul_inv_cancel _
  by_contra h_ne
  exact data.nontrivial_translation_nontrivial (P - Q) h_ne h_sub

end EllipticCurveIsogeny.KernelAutData

namespace EllipticCurveIsogeny.KernelAutData

/--
[translationPullback_injective_on_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean)
-/
@[path]
lemma translationPullback_injective_on_ker
  [Field F]
  [DecidableEq F] :
-- imply
  Function.Injective data.translationPullbackHomOnKer := by
-- proof
  intro ⟨P, hP⟩ ⟨Q, hQ⟩ h
  have h' : data.translationPullback P = data.translationPullback Q := by
    have := congr_arg Additive.toMul h
    simp only [translationPullbackHomOnKer, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    exact this
  exact Subtype.ext (data.translationPullback_injective h')

end EllipticCurveIsogeny.KernelAutData

namespace EllipticCurveIsogeny.KernelAutData

/--
[lemma_24_4_core](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean)
-/
@[path]
lemma lemma_24_4_core
  [Field F]
  [DecidableEq F] :
-- imply
  ∃ (f : φ_hom.ker →+ Additive (RingAut data.FunctionField)), Function.Injective f ∧ ∀ (P : φ_hom.ker) (x : data.PullbackField), (data.translationPullback P.val) (algebraMap data.PullbackField data.FunctionField x) = algebraMap data.PullbackField data.FunctionField x := by
-- proof
  refine ⟨data.translationPullbackHomOnKer, data.translationPullback_injective_on_ker, ?_⟩
  intro ⟨P, hP⟩ x
  exact data.translationPullback_fixes_image P hP x
variable {F : Type*} [Field F] [DecidableEq F]
  {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]

end EllipticCurveIsogeny.KernelAutData

namespace EllipticCurveIsogeny.TranslationPullbackData

/--
[lemma_24_4](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean)
-/
@[path]
lemma lemma_24_4
  [Field F]
  [DecidableEq F]
  {φ : EllipticCurveIsogeny W₁ W₂} :
-- imply
  ∃ (f : φ.ker →+ Additive (RingAut data.FunctionField)), Function.Injective f ∧ ∀ (P : φ.ker) (x : data.PullbackField), (data.translationPullback P.val) (algebraMap data.PullbackField data.FunctionField x) = algebraMap data.PullbackField data.FunctionField x := by
-- proof
  exact data.toKernelAutData.lemma_24_4_core

end EllipticCurveIsogeny.TranslationPullbackData


-- created on 2026-10-23
