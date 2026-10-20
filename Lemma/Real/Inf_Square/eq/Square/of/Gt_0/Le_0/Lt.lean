import Lemma.Real.Inf.eq.Mul.of.Gt_0
import Lemma.Real.Inf_Square.eq.Square.of.Le_0.Lt
open Real


@[path]
private lemma main
  {a m M : ℝ}
-- given
  (h₀ : a > 0)
  (h₁ : M ≤ 0)
  (h₂ : m < M) :
-- imply
  sInf ((fun x => x ^ 2 * a) '' Set.Ioo m M) = M ^ 2 * a := by
-- proof
  rw [Inf.eq.Mul.of.Gt_0 h₀ (f := fun x => x ^ 2),
    Inf_Square.eq.Square.of.Le_0.Lt h₁ h₂]
  ring


-- created on 2021-10-02
-- updated on 2026-10-17
