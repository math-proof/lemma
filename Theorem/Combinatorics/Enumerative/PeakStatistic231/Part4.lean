/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Fin
import Def.Combinatorics.Enumerative.PeakStatistic231.Part4


section

namespace MetaMathlibExt

namespace Peak231

theorem leftPerm_val {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a) (j : Fin a) :
    (leftPerm σ hAv hmax j).val = (σ ⟨j.val, by have hj := j.isLt; omega⟩).val := by
  have h : leftPerm σ hAv hmax j =
      (⟨(σ ⟨j.val, by have hj := j.isLt; omega⟩).val,
        joinMax_val_lt_of_avoids σ hAv hmax j.isLt⟩ : Fin a) := by
    simp only [leftPerm, Equiv.ofBijective_apply]
  have hcon := congrArg Fin.val h
  exact hcon

theorem rightPerm_bound {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a)
    (j : Fin b) (p : Fin (a + b + 1)) (hp : p.val = a + 1 + j.val) :
    (σ p).val - a < b := by
  have hlt := (σ p).isLt
  have hge : a ≤ (σ p).val :=
    joinMax_le_of_avoids (l := p) σ hAv hmax (by omega)
  have hne : (σ p).val ≠ a + b := by
    intro hcon
    have hsymm : σ.symm (Fin.last (a + b)) = (⟨a, by omega⟩ : Fin (a + b + 1)) :=
      Fin.ext hmax
    have htop : σ (⟨a, by omega⟩ : Fin (a + b + 1)) = Fin.last (a + b) := by
      have h := Equiv.apply_symm_apply σ (Fin.last (a + b))
      rwa [hsymm] at h
    have hpeq : p = (⟨a, by omega⟩ : Fin (a + b + 1)) := by
      apply σ.injective
      rw [htop]
      apply Fin.ext
      rw [Fin.val_last]
      exact hcon
    have hv : p.val = a := congrArg Fin.val hpeq
    omega
  omega

end Peak231
end MetaMathlibExt
end
