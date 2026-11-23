/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean -/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Order.Interval.Finset.Fin
public import Theorem.Combinatorics.Enumerative.PeakStatistic231.Part2

@[expose] public section

section

namespace MetaMathlibExt

namespace Peak231

noncomputable def joinMax {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
    Equiv.Perm (Fin (a + b + 1)) :=
  Equiv.ofBijective (joinMaxFun α β) (Finite.injective_iff_bijective.mp (joinMaxFun_inj α β))

end Peak231
end MetaMathlibExt
end
