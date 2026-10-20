import Lemma.Random.Var.eq.Sub.Expect
open MeasureTheory Random


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → ℝ}
-- given
  [PSpace π x]
  (h₀ : Integrable x π)
  (h₁ : Integrable (fun ω => x ω ^ 2) π) :
-- imply
  ∫ ω, x ω ^ 2 ∂π = (∫ ω, x ω ∂π) ^ 2 + 𝕍𝕒𝕣 π x := by
-- proof
  linarith [Var.eq.Sub.Expect (π := π) (x := x) h₀ h₁]


-- created on 2023-03-24
-- updated on 2026-10-17
