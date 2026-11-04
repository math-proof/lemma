import Def.Analysis.Real.Limits.Basic
import Def.Analysis.SpecialFunctions.Trigonometric
import Lemma.Hyperreal.Infinitesimal.is.XEq_0
import Lemma.Hyperreal.IsSt.is.Le0Mk.EqStdPart
open Hyperreal


@[path]
private lemma main
  {θ : ℝ*}
-- given
  (h : θ → 0) :
-- imply
  θ.sin ≈ θ.tan := by
-- proof
  obtain ⟨hx, hst⟩ := Le0Mk.EqStdPart.of.IsSt (x := θ) (r := 0) (by simpa using h)
  have h_tendsto : θ.Tendsto (nhds (0 : ℝ)) := by
    rw [tendsto_iff_forall]
    constructor <;>
      intro s hs
    ·
      exact (ArchimedeanClass.lt_of_lt_stdPart coeRingHom hx (by rwa [hst])).le
    ·
      exact (ArchimedeanClass.lt_of_stdPart_lt coeRingHom hx (by rwa [hst])).le
  have h_sin : θ.sin ≈ 0 := by
    apply XEq_0.of.Infinitesimal
    rw [Hyperreal.sin]
    apply archimedeanClassMk_pos_of_tendsto
    simpa [Real.sin_zero] using stdPart_map Real.continuous_sin.continuousAt h_tendsto
  have h_tan : θ.tan ≈ 0 := by
    apply XEq_0.of.Infinitesimal
    rw [Hyperreal.tan]
    apply archimedeanClassMk_pos_of_tendsto
    have htan : ContinuousAt Real.tan (0 : ℝ) := by
      rw [show Real.tan = fun x => Real.sin x / Real.cos x from funext Real.tan_eq_sin_div_cos]
      apply Real.continuous_sin.continuousAt.div Real.continuous_cos.continuousAt (Real.cos_zero.trans_ne one_ne_zero)
    simpa [Real.tan_zero] using stdPart_map htan h_tendsto
  apply h_sin.trans
  apply h_tan.symm


-- created on 2026-11-04
