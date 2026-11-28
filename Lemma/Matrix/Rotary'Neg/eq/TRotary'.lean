import Lemma.Matrix.RotaryOn__Neg.eq.TRotaryOn
open Matrix
open scoped Matrix


/-- Negating the angles transposes the interleaved rotary matrix: \(R(-\theta) = R(\theta)^{\mathsf{T}}\). -/
@[path]
private lemma main
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  Matrix.rotary' (-φ) = (Matrix.rotary' φ)ᵀ := by
-- proof
  simpa [Matrix.rotary'] using RotaryOn__Neg.eq.TRotaryOn (u := Fin.stepEven) (v := Fin.stepOdd) φ


-- created on 2026-11-26
-- updated on 2026-11-28
