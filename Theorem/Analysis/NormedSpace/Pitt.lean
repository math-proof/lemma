/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


section

namespace FunctionalAnalysis.PittWanted

/-- `0 < q.toReal` for `1 ≤ q` with `q ≠ ⊤`. -/
lemma toReal_pos_of_one_le {q : ENNReal} [Fact (1 ≤ q)] (hq : q ≠ ⊤) :
    0 < q.toReal := by
  apply ENNReal.toReal_pos _ hq
  exact (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne'

/-- `1 ≤ q.toReal` for `1 ≤ q` with `q ≠ ⊤`. -/
lemma one_le_toReal_of_one_le {q : ENNReal} [Fact (1 ≤ q)] (hq : q ≠ ⊤) :
    1 ≤ q.toReal := by
  have h := ENNReal.toReal_le_toReal ENNReal.one_ne_top hq
  simpa using h.mpr (Fact.out : 1 ≤ q)

end FunctionalAnalysis.PittWanted
end
