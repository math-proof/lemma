/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Fin
import Def.Combinatorics.Enumerative.PeakStatistic231.Part3


section

namespace MetaMathlibExt

namespace Peak231

-- N5
theorem joinMax_lt_of_avoids_aux {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a)
    {i l : Fin (a + b + 1)} (hi : i.val < a) (hl : a < l.val) : σ i < σ l := by
  set pos : Fin (a + b + 1) := ⟨a, by omega⟩ with hpos
  set last : Fin (a + b + 1) := Fin.last (a + b) with hlast
  have hsymm : σ.symm last = pos := Fin.ext hmax
  have htop : σ pos = last := by rw [← hsymm, Equiv.apply_symm_apply]
  have hne_i : σ i ≠ last := by
    intro hcon
    have hi2 : i = pos := σ.injective (by rw [hcon, htop])
    have hv : i.val = a := congrArg Fin.val hi2
    omega
  have hne_i' : σ i ≠ Fin.last (a + b) := by rwa [hlast] at hne_i
  have hi_lt : σ i < σ pos := by
    rw [htop, hlast]
    exact Fin.lt_last_iff_ne_last.mpr hne_i'
  have o1 : i < pos := by
    rw [hpos]
    exact Fin.lt_def.mpr hi
  have o2 : pos < l := by
    rw [hpos]
    exact Fin.lt_def.mpr hl
  have hnot := hAv i pos l o1 o2
  have hle : σ i ≤ σ l := le_of_not_gt (fun hcon => hnot ⟨hcon, hi_lt⟩)
  have hne : σ i ≠ σ l := by
    intro hcon
    have h2 : i = l := σ.injective hcon
    have hv : i.val = l.val := congrArg Fin.val h2
    omega
  exact lt_of_le_of_ne hle hne

theorem joinMax_val_lt_of_avoids {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a)
    {i : Fin (a + b + 1)} (hi : i.val < a) : (σ i).val < a := by
  set pos : Fin (a + b + 1) := ⟨a, by omega⟩ with hpos
  set last : Fin (a + b + 1) := Fin.last (a + b) with hlast
  have hposv : pos.val = a := by rw [hpos]
  have hlastv : last.val = a + b := by
    rw [hlast]
    exact Fin.val_last _
  have hsymm : σ.symm last = pos := Fin.ext hmax
  have htop : σ pos = last := by rw [← hsymm, Equiv.apply_symm_apply]
  have hne_last : ∀ x : Fin (a + b + 1), x.val ≠ a → σ x ≠ last := by
    intro x hx hcon
    have hx2 : x = pos := σ.injective (by rw [hcon, htop])
    have hv : x.val = a := congrArg Fin.val hx2
    exact hx hv
  have hlt_top : (σ i).val < a + b := by
    have h := (σ i).isLt
    have hne : (σ i).val ≠ a + b := by
      intro hcon
      apply hne_last i (by omega)
      apply Fin.ext
      rw [hlastv]
      exact hcon
    omega
  have hs : (Finset.Ioi pos).card = b := by
    have h : (Finset.Ioi pos).card = (a + b + 1) - 1 - pos.val := Fin.card_Ioi pos
    omega
  have ht : (Finset.Ioo (σ i) last).card = last.val - (σ i).val - 1 :=
    Fin.card_Ioo (σ i) last
  have hmaps : Set.MapsTo σ (↑(Finset.Ioi pos)) (↑(Finset.Ioo (σ i) last)) := by
    intro l hl
    rw [Finset.mem_coe, Finset.mem_Ioi] at hl
    rw [Finset.mem_coe, Finset.mem_Ioo]
    have hlv : a < l.val := by
      have h := Fin.lt_def.mp hl
      omega
    have h1 : σ i < σ l := joinMax_lt_of_avoids_aux σ hAv hmax hi hlv
    have hne_l : σ l ≠ last := hne_last l (by omega)
    have h2 : σ l < last := by
      rw [hlast]
      apply Fin.lt_last_iff_ne_last.mpr
      rwa [hlast] at hne_l
    exact ⟨h1, h2⟩
  have hinj : Set.InjOn σ (↑(Finset.Ioi pos)) := fun _ _ _ _ h => σ.injective h
  have hle := Finset.card_le_card_of_injOn σ hmaps hinj
  omega

theorem joinMax_le_of_avoids {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a)
    {l : Fin (a + b + 1)} (hl : a < l.val) : a ≤ (σ l).val := by
  set pos : Fin (a + b + 1) := ⟨a, by omega⟩ with hpos
  have hposv : pos.val = a := by rw [hpos]
  have hs : (Finset.Iio pos).card = a := by
    have h : (Finset.Iio pos).card = pos.val := Fin.card_Iio pos
    omega
  have ht : (Finset.Iio (σ l)).card = (σ l).val := Fin.card_Iio (σ l)
  have hmaps : Set.MapsTo σ (↑(Finset.Iio pos)) (↑(Finset.Iio (σ l))) := by
    intro i hi
    rw [Finset.mem_coe, Finset.mem_Iio] at hi
    rw [Finset.mem_coe, Finset.mem_Iio]
    have hiv : i.val < a := by
      have h := Fin.lt_def.mp hi
      omega
    exact joinMax_lt_of_avoids_aux σ hAv hmax hiv hl
  have hinj : Set.InjOn σ (↑(Finset.Iio pos)) := fun _ _ _ _ h => σ.injective h
  have hle := Finset.card_le_card_of_injOn σ hmaps hinj
  omega

end Peak231
end MetaMathlibExt
end
