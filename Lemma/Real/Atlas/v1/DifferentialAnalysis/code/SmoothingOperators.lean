import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.SmoothingOperators
open MvPolynomial SchwartzMap SmoothingOperators
open scoped SchwartzMap
open scoped LineDeriv


namespace SmoothingOperators

/--
[smoothing_produces_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SmoothingOperators.lean)
-/
@[path]
lemma smoothing_produces_smooth
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {u : 𝓢'(E, ℂ)}
  {φ : 𝓢(E, ℂ)} :
-- imply
  ContDiff ℝ (⊤ : ℕ∞) (fun x : E => u (compSubConstCLM ℂ x φ)) :=
-- proof
  DifferentialOperators.contDiff_schwartz_translation_clm u φ

end SmoothingOperators

namespace SmoothingOperators

/--
[schwartz_translation_fderiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SmoothingOperators.lean)
-/
@[path]
lemma schwartz_translation_fderiv_apply
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {L : 𝓢(E, ℂ) →L[ℂ] F}
  {ψ : 𝓢(E, ℂ)}
-- given
  (x h : E) :
-- imply
  fderiv ℝ (fun z => L (compSubConstCLM ℂ z ψ)) x h = L (compSubConstCLM ℂ x (∂_{-h} ψ)) := by
-- proof
  have hlinederiv_eq : (∂_{-h} ψ : 𝓢(E, ℂ)) =
    -(SchwartzMap.evalCLM ℂ E ℂ h (SchwartzMap.fderivCLM ℂ E ℂ ψ)) := by
    ext y
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.neg_apply,
      SchwartzMap.evalCLM_apply_apply, SchwartzMap.fderivCLM_apply, map_neg]
  set ψ' := SchwartzMap.fderivCLM ℂ E ℂ ψ
  set g : E →L[ℝ] F :=
    -({ toFun := fun v => L (compSubConstCLM ℂ x (SchwartzMap.evalCLM ℂ E ℂ v ψ'))
      map_add' := by
        intro h₁ h₂
        have : SchwartzMap.evalCLM ℂ E ℂ (h₁ + h₂) ψ' =
          SchwartzMap.evalCLM ℂ E ℂ h₁ ψ' + SchwartzMap.evalCLM ℂ E ℂ h₂ ψ' := by
          ext y; simp only [SchwartzMap.evalCLM_apply_apply, map_add, SchwartzMap.add_apply]
        rw [this, map_add, map_add]
      map_smul' := by
        intro r v
        simp only [RingHom.id_apply]
        have : SchwartzMap.evalCLM ℂ E ℂ (r • v) ψ' =
          (r : ℂ) • SchwartzMap.evalCLM ℂ E ℂ v ψ' := by
          ext y
          simp only [SchwartzMap.evalCLM_apply_apply, SchwartzMap.smul_apply, map_smul]; rfl
        rw [this, map_smul, map_smul]; rfl } : E →ₗ[ℝ] F).toContinuousLinearMap
  suffices hfd : HasFDerivAt (fun z => L (compSubConstCLM ℂ z ψ)) g x by
    rw [hfd.fderiv]
    show g h = L (compSubConstCLM ℂ x (∂_{-h} ψ))
    simp only [g, ContinuousLinearMap.neg_apply]
    show -L (compSubConstCLM ℂ x (SchwartzMap.evalCLM ℂ E ℂ h ψ')) =
      L (compSubConstCLM ℂ x (∂_{-h} ψ))
    rw [hlinederiv_eq, map_neg, map_neg]
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hrw : ∀ v : E,
    L (compSubConstCLM ℂ (x + v) ψ) - L (compSubConstCLM ℂ x ψ) - g v =
    L (compSubConstCLM ℂ x
      (compSubConstCLM ℂ v ψ - ψ + SchwartzMap.evalCLM ℂ E ℂ v ψ')) := by
    intro v
    have hcomp : compSubConstCLM ℂ (x + v) ψ =
      compSubConstCLM ℂ x (compSubConstCLM ℂ v ψ) := by
      rw [SchwartzMap.compSubConstCLM_comp]; congr 1; abel
    have hg : g v = -L (compSubConstCLM ℂ x (SchwartzMap.evalCLM ℂ E ℂ v ψ')) := rfl
    rw [hcomp, hg, sub_neg_eq_add, ← map_sub L, ← map_add L,
      ← map_sub (compSubConstCLM ℂ x), ← map_add (compSubConstCLM ℂ x)]
  simp_rw [hrw]
  exact DifferentialOperators.schwartz_taylor_remainder_isLittleO L ψ x

end SmoothingOperators

namespace SmoothingOperators

/--
[smoothing_lineDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SmoothingOperators.lean)
-/
@[path]
lemma smoothing_lineDeriv
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {u : 𝓢'(E, ℂ)}
  {φ : 𝓢(E, ℂ)}
  {m : E}
  {x : E} :
-- imply
  lineDeriv ℝ (fun z : E => u (compSubConstCLM ℂ z φ)) x m = u (compSubConstCLM ℂ x (∂_{-m} φ)) := by
-- proof
  have hdiff : DifferentiableAt ℝ (fun z => u (compSubConstCLM ℂ z φ)) x :=
    (DifferentialOperators.contDiff_schwartz_translation_clm u φ).differentiable (by simp)
      |>.differentiableAt
  rw [hdiff.lineDeriv_eq_fderiv]
  exact schwartz_translation_fderiv_apply u φ x m
end SmoothingOperators
namespace DifferentialOperators



-- created on 2026-10-23
