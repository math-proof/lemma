import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.FunctionalAnalysis.BanachSaks
open MathlibExt.Analysis.FunctionalAnalysis.BanachSaksWanted


/--
[banach_saks](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/BanachSaks.lean)
-/
@[path]
private lemma banach_saks_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E] [CompleteSpace E]
  {x : ℕ → E}
-- given
  (hx : Bornology.IsBounded (Set.range x)) :
-- imply
  ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (y : E),
    Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, x (φ i)) Filter.atTop (nhds y) := by
-- proof
  apply MathlibExt.Analysis.FunctionalAnalysis.BanachSaksWanted.banach_saks hx


-- created on 2026-10-20
