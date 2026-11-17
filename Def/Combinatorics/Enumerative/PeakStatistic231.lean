/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean -/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Order.Interval.Finset.Fin
public import Abbrev.Combinatorics.Enumerative.PeakStatistic231

@[expose] public section

section

namespace MetaMathlibExt

namespace Peak231

def avoidCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    Avoids231 σ ∧ peakCount σ = k)).card

end Peak231
end MetaMathlibExt
end
