import Def.Analysis.Real.Limits.Basic
import Def.Analysis.SpecialFunctions.Trigonometric
import Lemma.Hyperreal.IsSt.is.Le0Mk.EqStdPart
import Lemma.Hyperreal.UFn.of.All_UFn
import Lemma.Hyperreal.XEq.of.InfinitesimalSub
open Filter Hyperreal


@[path]
private lemma main
  {θ : ℝ*}
-- given
  (h : θ → 0)
  (h_tan : θ.tan ≠ 0) :
-- imply
  θ.sin / θ.tan ≈ 1 := by
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
  have h_cos : (θ.cos - (1 : ℝ)) → 0 := by
    rw [Hyperreal.cos]
    apply IsSt.of.Le0Mk.EqStdPart
    ·
      apply archimedeanClassMk_nonneg_of_tendsto
      simpa [Real.cos_zero] using stdPart_map Real.continuous_cos.continuousAt h_tendsto
    ·
      apply stdPart_of_tendsto
      simpa [Real.cos_zero] using stdPart_map Real.continuous_cos.continuousAt h_tendsto
  have h_eq : θ.sin / θ.tan = θ.cos := by
    revert h_tan
    apply UFn.of.All_UFn θ
    intro f hf
    dsimp only [Hyperreal.sin, Hyperreal.tan, Hyperreal.cos] at hf ⊢
    apply Germ.coe_eq.mpr
    have hne : ∀ᶠ n in hyperfilter ℕ, Real.tan (f n) ≠ 0 := by
      rw [Ultrafilter.eventually_not]
      intro hall
      apply hf
      apply Germ.coe_eq.mpr hall
    filter_upwards [hne] with n hn
    change Real.sin (f n) / Real.tan (f n) = Real.cos (f n)
    have hsin : Real.sin (f n) ≠ 0 := by
      intro hs
      apply hn
      rw [Real.tan_eq_sin_div_cos, hs, zero_div]
    rw [Real.tan_eq_sin_div_cos, div_eq_mul_inv, inv_div, ← mul_div_assoc]
    apply mul_div_cancel_left₀ _ hsin
  rw [h_eq]
  apply XEq.of.InfinitesimalSub h_cos


-- created on 2026-11-04
