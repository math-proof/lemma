/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

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
