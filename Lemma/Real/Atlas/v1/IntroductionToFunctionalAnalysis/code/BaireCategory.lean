import Mathlib
import Initialize.Tactic.Attr.Basic
open Set Topology


/--
[baire_category_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/BaireCategory.lean)
-/
@[path]
lemma baire_category_theorem
  [MetricSpace M]
  [CompleteSpace M]
  [Nonempty M]
  {C : ℕ → Set M}
-- given
  (hc : ∀ n, IsClosed (C n))
  (hU : ⋃ n, C n = univ) :
-- imply
  ∃ n, (interior (C n)).Nonempty :=
-- proof
  nonempty_interior_of_iUnion_of_closed hc hU


-- created on 2026-10-24
