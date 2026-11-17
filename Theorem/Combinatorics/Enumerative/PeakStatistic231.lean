/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean -/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Order.Interval.Finset.Fin
public import Def.Combinatorics.Enumerative.PeakStatistic231

public section

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
