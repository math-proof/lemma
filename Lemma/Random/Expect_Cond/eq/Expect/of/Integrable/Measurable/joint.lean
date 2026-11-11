import Instance.Probability.Moments.Variance
import Lemma.Random.Expect_Cond.eq.Expect.of.Integrable.Measurable
open MeasureTheory Random


/--
Law of iterated expectations over two finite-valued random variables `Y`, `Z`:
`𝔼_{Y, Z}[𝔼[f | Y, Z]] = 𝔼[f]`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
  [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype β]
  {μ : Measure Ω} {Y : Ω → α} [PSpace μ Y]
  {Z : Ω → β} [PSpace μ Z]
  {f : Ω → ℝ} [PSpace μ f]
-- given
  (hY : Measurable Y)
  (hZ : Measurable Z)
  (hf : Integrable f μ) :
-- imply
  𝔼[Y, Z: μ](𝔼[f: μ](f | Y, Z)) = 𝔼[f: μ](f) := by
-- proof
  apply Expect_Cond.eq.Expect.of.Integrable.Measurable (X := (Y, Z)) (hY.prodMk hZ) hf


-- created on 2023-04-01
-- updated on 2026-11-10
