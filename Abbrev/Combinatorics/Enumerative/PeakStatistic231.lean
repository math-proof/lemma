/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean -/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section


section

namespace MetaMathlibExt

namespace Peak231

abbrev Avoids231 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j l : Fin n, i < j → j < l → ¬ (σ l < σ i ∧ σ i < σ j)

abbrev IsPeakAt {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∃ iPrev iNext : Fin n,
    iPrev.val + 1 = i.val ∧ i.val + 1 = iNext.val ∧
    σ iPrev < σ i ∧ σ iNext < σ i

abbrev peakCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => IsPeakAt σ i)).card

end Peak231
end MetaMathlibExt
end
