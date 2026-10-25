/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Fin
import Def.Combinatorics.Enumerative.PeakStatistic231.Part2


section

namespace MetaMathlibExt

namespace Peak231

theorem joinMaxFun_inj {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
    Function.Injective (joinMaxFun α β) := by
  intro i j hij
  have hval := congrArg Fin.val hij
  simp only [joinMaxFun] at hval
  have hi1 : i.val < a + b + 1 := i.isLt
  have hj1 : j.val < a + b + 1 := j.isLt
  have hlast : (Fin.last (a + b)).val = a + b := Fin.val_last _
  by_cases hiL : i.val < a <;> by_cases hiM : i.val = a <;>
    by_cases hjL : j.val < a <;> by_cases hjM : j.val = a
  · omega  -- TTTT contra
  · omega  -- TTTF contra
  · omega  -- TTFT contra
  · omega  -- TTFF contra
  · omega  -- TFTT contra j
  · -- TFTF left,left
    simp only [dite_eq_left hiL, dite_eq_left hjL] at hval
    have ha : (⟨i.val, hiL⟩ : Fin a) = ⟨j.val, hjL⟩ :=
      α.injective (Fin.ext hval)
    have hvv := congrArg Fin.val ha
    exact Fin.ext hvv
  · -- TFFT left,mid
    simp only [dite_eq_left hiL, dite_eq_right hjL, dite_eq_left hjM] at hval
    exfalso
    have hα : (α ⟨i.val, hiL⟩).val < a := (α ⟨i.val, hiL⟩).isLt
    omega
  · -- TFFF left,right
    simp only [dite_eq_left hiL, dite_eq_right hjL, dite_eq_right hjM] at hval
    exfalso
    have hα : (α ⟨i.val, hiL⟩).val < a := (α ⟨i.val, hiL⟩).isLt
    have hβ : (β ⟨j.val - a - 1, by omega⟩).val < b :=
      (β ⟨j.val - a - 1, by omega⟩).isLt
    omega
  · omega  -- FTTT contra j
  · -- FTTF mid,left
    simp only [dite_eq_right hiL, dite_eq_left hiM, dite_eq_left hjL] at hval
    exfalso
    have hα : (α ⟨j.val, hjL⟩).val < a := (α ⟨j.val, hjL⟩).isLt
    omega
  · -- FTFT mid,mid
    simp only [dite_eq_right hiL, dite_eq_left hiM,
      dite_eq_right hjL, dite_eq_left hjM] at hval
    have hv : i.val = j.val := by omega
    exact Fin.ext hv
  · -- FTFF mid,right
    simp only [dite_eq_right hiL, dite_eq_left hiM,
      dite_eq_right hjL, dite_eq_right hjM] at hval
    exfalso
    have hβ : (β ⟨j.val - a - 1, by omega⟩).val < b :=
      (β ⟨j.val - a - 1, by omega⟩).isLt
    omega
  · omega  -- FFTT contra j
  · -- FFTF right,left
    simp only [dite_eq_right hiL, dite_eq_right hiM, dite_eq_left hjL] at hval
    exfalso
    have hα : (α ⟨j.val, hjL⟩).val < a := (α ⟨j.val, hjL⟩).isLt
    have hβ : (β ⟨i.val - a - 1, by omega⟩).val < b :=
      (β ⟨i.val - a - 1, by omega⟩).isLt
    omega
  · -- FFFT right,mid
    simp only [dite_eq_right hiL, dite_eq_right hiM,
      dite_eq_right hjL, dite_eq_left hjM] at hval
    exfalso
    have hβ : (β ⟨i.val - a - 1, by omega⟩).val < b :=
      (β ⟨i.val - a - 1, by omega⟩).isLt
    omega
  · -- FFFF right,right
    simp only [dite_eq_right hiL, dite_eq_right hiM,
      dite_eq_right hjL, dite_eq_right hjM] at hval
    have hb : (⟨i.val - a - 1, by omega⟩ : Fin b) = ⟨j.val - a - 1, by omega⟩ := by
      apply β.injective
      apply Fin.ext
      omega
    have hv : i.val - a - 1 = j.val - a - 1 := by exact congrArg Fin.val hb
    have hv2 : i.val = j.val := by omega
    exact Fin.ext hv2

end Peak231
end MetaMathlibExt
end
