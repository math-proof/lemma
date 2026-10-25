/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Fin
import Theorem.Combinatorics.Enumerative.PeakStatistic231.Part2


section

namespace MetaMathlibExt

namespace Peak231

noncomputable def joinMax {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
    Equiv.Perm (Fin (a + b + 1)) :=
  Equiv.ofBijective (joinMaxFun α β) (Finite.injective_iff_bijective.mp (joinMaxFun_inj α β))

end Peak231
end MetaMathlibExt
end
