/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Fin
import Theorem.Combinatorics.Enumerative.PeakStatistic231.Part3


section

namespace MetaMathlibExt

namespace Peak231

-- N6
noncomputable def leftPerm {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a) :
    Equiv.Perm (Fin a) :=
  Equiv.ofBijective (fun j : Fin a =>
    (⟨(σ ⟨j.val, by have hj := j.isLt; omega⟩).val,
      joinMax_val_lt_of_avoids σ hAv hmax j.isLt⟩ : Fin a))
    (Finite.injective_iff_bijective.mp (by
      intro j1 j2 h12
      have hcon := congrArg Fin.val h12
      have hv : (σ ⟨j1.val, by have hj := j1.isLt; omega⟩).val =
          (σ ⟨j2.val, by have hj := j2.isLt; omega⟩).val := hcon
      have hpos : (⟨j1.val, by have hj := j1.isLt; omega⟩ : Fin (a + b + 1)) =
          ⟨j2.val, by have hj := j2.isLt; omega⟩ :=
        σ.injective (Fin.ext hv)
      have hcon2 := congrArg Fin.val hpos
      have hv2 : j1.val = j2.val := hcon2
      exact Fin.ext hv2))

end Peak231
end MetaMathlibExt
end
