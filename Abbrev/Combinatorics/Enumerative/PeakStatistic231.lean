/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Fin


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
