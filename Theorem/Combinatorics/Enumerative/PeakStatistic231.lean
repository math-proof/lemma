/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Fin
import Def.Combinatorics.Enumerative.PeakStatistic231


section

namespace MetaMathlibExt

namespace Peak231

-- bridge: Wanted LHS is avoidCount by rfl
example (n k : ℕ) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (∀ i j l : Fin n, i < j → j < l → ¬ (σ l < σ i ∧ σ i < σ j)) ∧
      (Finset.univ.filter (fun i : Fin n =>
        ∃ iPrev iNext : Fin n,
          iPrev.val + 1 = i.val ∧ i.val + 1 = iNext.val ∧
          σ iPrev < σ i ∧ σ iNext < σ i)).card = k)).card =
    avoidCount n k := rfl

end Peak231
end MetaMathlibExt
end
