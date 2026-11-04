import Def.Analysis.Real.Limits.Basic
import Def.Analysis.SpecialFunctions.Trigonometric
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.IsSt.is.Le0Mk.EqStdPart
import Lemma.Hyperreal.XEq.of.InfinitesimalSub
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
  apply XEq.of.InfinitesimalSub
  apply InfinitesimalSub.of.Infinitesimal.Infinitesimal
  ·
    rw [Hyperreal.sin]
    apply archimedeanClassMk_pos_of_tendsto
    simpa [Real.sin_zero] using stdPart_map Real.continuous_sin.continuousAt h_tendsto
  ·
    rw [Hyperreal.tan]
    apply archimedeanClassMk_pos_of_tendsto
    have htan : ContinuousAt Real.tan (0 : ℝ) := by
      rw [show Real.tan = fun x => Real.sin x / Real.cos x from funext Real.tan_eq_sin_div_cos]
      apply Real.continuous_sin.continuousAt.div Real.continuous_cos.continuousAt (Real.cos_zero.trans_ne one_ne_zero)
    simpa [Real.tan_zero] using stdPart_map htan h_tendsto


-- created on 2026-11-04
