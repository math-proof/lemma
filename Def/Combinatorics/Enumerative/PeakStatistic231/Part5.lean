/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Fin
import Theorem.Combinatorics.Enumerative.PeakStatistic231.Part4


section

namespace MetaMathlibExt

namespace Peak231

noncomputable def rightPerm {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a) :
    Equiv.Perm (Fin b) :=
  Equiv.ofBijective (fun j : Fin b =>
    (⟨(σ ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩).val - a,
      rightPerm_bound σ hAv hmax j ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩
        rfl⟩ : Fin b))
    (Finite.injective_iff_bijective.mp (by
      intro j1 j2 h12
      have hcon := congrArg Fin.val h12
      set p1 : Fin (a + b + 1) := ⟨a + 1 + j1.val, by have hj := j1.isLt; omega⟩ with hp1def
      set p2 : Fin (a + b + 1) := ⟨a + 1 + j2.val, by have hj := j2.isLt; omega⟩ with hp2def
      have hp1v : p1.val = a + 1 + j1.val := rfl
      have hp2v : p2.val = a + 1 + j2.val := rfl
      have hv : (σ p1).val - a = (σ p2).val - a := hcon
      have hg1 : a ≤ (σ p1).val :=
        joinMax_le_of_avoids (l := p1) σ hAv hmax (by omega)
      have hg2 : a ≤ (σ p2).val :=
        joinMax_le_of_avoids (l := p2) σ hAv hmax (by omega)
      have hv' : (σ p1).val = (σ p2).val := by omega
      have hpos : p1 = p2 := σ.injective (Fin.ext hv')
      have hcon2 := congrArg Fin.val hpos
      have hv2 : j1.val = j2.val := by omega
      exact Fin.ext hv2))

end Peak231
end MetaMathlibExt
end
