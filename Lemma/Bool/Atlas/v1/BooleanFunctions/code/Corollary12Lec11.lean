import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.UGCHardness


namespace UGCHardness

/--
[corollary_1_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Corollary12Lec11.lean)
-/
@[path]
lemma corollary_1_2
-- given
  (hUGC : UGC) :
-- imply
  ∀ ε : ℝ, ε > 0 → MaxCut.IsNPHardGapMaxCut (1 - ε) (MaxCut.goemansWilliamsonConstant + ε) :=
-- proof
  goemansWilliamson_optimal_assuming_ugc hUGC

end UGCHardness


-- created on 2026-10-23
