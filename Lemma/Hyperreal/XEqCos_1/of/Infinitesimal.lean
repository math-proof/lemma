import Def.Analysis.SpecialFunctions.Trigonometric
import Lemma.Hyperreal.XEq.of.InfinitesimalSub
open Filter Hyperreal


@[path]
private lemma main
  {θ : ℝ*}
-- given
  (h : θ → 0) :
-- imply
  θ.cos ≈ 1 := by
-- proof
  obtain ⟨hx, hst⟩ := Le0Mk.EqStdPart.of.IsSt (x := θ) (r := 0) (by simpa using h)
  have h_tendsto : θ.Tendsto (nhds (0 : ℝ)) := by
    rw [tendsto_iff_forall]
    constructor <;>
      intro s hs
    ·
      apply (ArchimedeanClass.lt_of_lt_stdPart coeRingHom hx (by rwa [hst])).le
    ·
      apply (ArchimedeanClass.lt_of_stdPart_lt coeRingHom hx (by rwa [hst])).le
  apply XEq.of.InfinitesimalSub
  rw [Hyperreal.cos]
  apply IsSt.of.Le0Mk.EqStdPart
  ·
    apply archimedeanClassMk_nonneg_of_tendsto
    simpa [Real.cos_zero] using stdPart_map Real.continuous_cos.continuousAt h_tendsto
  ·
    apply stdPart_of_tendsto
    simpa [Real.cos_zero] using stdPart_map Real.continuous_cos.continuousAt h_tendsto


-- created on 2026-11-05
