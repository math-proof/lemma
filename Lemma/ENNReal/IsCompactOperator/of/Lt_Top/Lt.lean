import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.NormedSpace.Pitt.Part2

/--
[Pitt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/Pitt.lean)
-/
@[path]
private lemma pitt_is
-- given
  {𝕜 : Type*} [RCLike 𝕜]
  (p q : ENNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  (hq_lt : q < p)
  (hp_lt : p < ⊤)
  (T : lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) q) :
-- imply
  IsCompactOperator T := by
-- proof
  apply FunctionalAnalysis.PittWanted.pitt p q hq_lt hp_lt T

-- created on 2026-10-10
