import Lemma.Real.Inf_Square.eq.Zero.of.Gt_0.Lt_0
import Lemma.Real.Inf_Square.eq.Square.of.Ge_0.Lt
open Real


@[path]
private lemma main
  {m M : ℝ}
-- given
  (h₀ : m ≤ 0)
  (h₁ : 0 < M) :
-- imply
  sInf ((fun x => x ^ 2) '' Set.Ioo m M) = 0 := by
-- proof
  if hm : m < 0 then
    apply Inf_Square.eq.Zero.of.Gt_0.Lt_0 h₁ hm
  else
    have hm0 : m = 0 := le_antisymm h₀ (le_of_not_gt hm)
    subst hm0
    simpa using Inf_Square.eq.Square.of.Ge_0.Lt (m := (0 : ℝ)) (M := M) le_rfl h₁


-- created on 2026-10-11
-- updated on 2026-10-17
