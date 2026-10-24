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

private abbrev Avoids231 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j l : Fin n, i < j → j < l → ¬ (σ l < σ i ∧ σ i < σ j)

private abbrev IsPeakAt {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∃ iPrev iNext : Fin n,
    iPrev.val + 1 = i.val ∧ i.val + 1 = iNext.val ∧
    σ iPrev < σ i ∧ σ iNext < σ i

private abbrev peakCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => IsPeakAt σ i)).card

private def avoidCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    Avoids231 σ ∧ peakCount σ = k)).card

-- bridge: Wanted LHS is avoidCount by rfl
example (n k : ℕ) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (∀ i j l : Fin n, i < j → j < l → ¬ (σ l < σ i ∧ σ i < σ j)) ∧
      (Finset.univ.filter (fun i : Fin n =>
        ∃ iPrev iNext : Fin n,
          iPrev.val + 1 = i.val ∧ i.val + 1 = iNext.val ∧
          σ iPrev < σ i ∧ σ iNext < σ i)).card = k)).card =
    avoidCount n k := rfl

private def peakConv (F : ℕ → ℕ → ℕ) (a b k : ℕ) : ℕ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, F a p.1 * F b p.2

private def peakRec (F : ℕ → ℕ → ℕ) (n k : ℕ) : ℕ :=
  ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
    (if q.1 = 0 ∨ q.2 = 0 then peakConv F q.1 q.2 k
     else (if k = 0 then 0 else peakConv F q.1 q.2 (k - 1)))

private def peakV (n p : ℕ) : ℕ :=
  if n = 0 then 0 else 2 ^ (n - p - 1) * Nat.choose (n - 1) p

private def peakT (n k : ℕ) : ℕ :=
  2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) * catalan k

private def peakU : PowerSeries ℕ :=
  PowerSeries.mk fun m => if m = 0 then 0 else 2 ^ (m - 1)

-- N1
private def joinMaxFun {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
    Fin (a + b + 1) → Fin (a + b + 1) :=
  fun i =>
    if h1 : i.val < a then ⟨(α ⟨i.val, h1⟩).val, by have h2 := (α ⟨i.val, h1⟩).isLt; omega⟩
    else if _h2 : i.val = a then Fin.last (a + b)
    else ⟨a + (β ⟨i.val - a - 1, by have h3 := i.isLt; omega⟩).val,
      by have h4 := (β ⟨i.val - a - 1, by have h3 := i.isLt; omega⟩).isLt
         have h3 := i.isLt; omega⟩

private theorem joinMaxFun_inj {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
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

private noncomputable def joinMax {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
    Equiv.Perm (Fin (a + b + 1)) :=
  Equiv.ofBijective (joinMaxFun α β) (Finite.injective_iff_bijective.mp (joinMaxFun_inj α β))

-- N5
private theorem joinMax_lt_of_avoids_aux {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
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

private theorem joinMax_val_lt_of_avoids {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
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

private theorem joinMax_le_of_avoids {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
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

-- N6
private noncomputable def leftPerm {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
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

private theorem leftPerm_val {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a) (j : Fin a) :
    (leftPerm σ hAv hmax j).val = (σ ⟨j.val, by have hj := j.isLt; omega⟩).val := by
  have h : leftPerm σ hAv hmax j =
      (⟨(σ ⟨j.val, by have hj := j.isLt; omega⟩).val,
        joinMax_val_lt_of_avoids σ hAv hmax j.isLt⟩ : Fin a) := by
    simp only [leftPerm, Equiv.ofBijective_apply]
  have hcon := congrArg Fin.val h
  exact hcon

private theorem rightPerm_bound {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
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

private noncomputable def rightPerm {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
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

private theorem rightPerm_val {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a) (j : Fin b) :
    (rightPerm σ hAv hmax j).val =
      (σ ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩).val - a := by
  have h : rightPerm σ hAv hmax j =
      (⟨(σ ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩).val - a,
        rightPerm_bound σ hAv hmax j ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩
          rfl⟩ : Fin b) := by
    simp only [rightPerm, Equiv.ofBijective_apply]
  have hcon := congrArg Fin.val h
  exact hcon

private theorem exists_joinMax_eq {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a) :
    ∃ α β, joinMax α β = σ := by
  refine ⟨leftPerm σ hAv hmax, rightPerm σ hAv hmax, ?_⟩
  apply Equiv.ext
  intro p
  apply Fin.ext
  by_cases hlt : p.val < a
  · have e1 := joinMax_apply_lt (leftPerm σ hAv hmax) (rightPerm σ hAv hmax)
      (i := p) hlt
    rw [e1]
    have e2 := leftPerm_val σ hAv hmax ⟨p.val, hlt⟩
    rw [e2]
  · by_cases heq : p.val = a
    · have e1 := joinMax_val_of_eq (leftPerm σ hAv hmax) (rightPerm σ hAv hmax)
        (p := p) heq
      rw [e1]
      have hsymm : σ.symm (Fin.last (a + b)) = (⟨a, by omega⟩ : Fin (a + b + 1)) :=
        Fin.ext hmax
      have htop : σ (⟨a, by omega⟩ : Fin (a + b + 1)) = Fin.last (a + b) := by
        have h := Equiv.apply_symm_apply σ (Fin.last (a + b))
        rwa [hsymm] at h
      have hp : p = ⟨a, by omega⟩ := Fin.ext heq
      rw [hp, htop, Fin.val_last]
    · have hgt : a < p.val := by omega
      have e1 := joinMax_apply_gt (leftPerm σ hAv hmax) (rightPerm σ hAv hmax)
        (i := p) hgt
      rw [e1]
      have e2 := rightPerm_val σ hAv hmax
        ⟨p.val - a - 1, by have hp := p.isLt; omega⟩
      rw [e2]
      have hpp : (⟨a + 1 + (⟨p.val - a - 1, by have hp := p.isLt; omega⟩ : Fin b).val,
          by have hp := p.isLt; omega⟩ : Fin (a + b + 1)) = p := by
        apply Fin.ext
        change a + 1 + (p.val - a - 1) = p.val
        omega
      rw [hpp]
      have hge := joinMax_le_of_avoids (l := p) σ hAv hmax hgt
      omega

-- N7
private theorem card_fiber_joinMax {a b n k : ℕ} (hab : a + b = n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
      ((Avoids231 σ ∧ peakCount σ = k) ∧ (σ.symm (Fin.last n)).val = a))).card =
    (((Finset.univ.filter (fun α : Equiv.Perm (Fin a) => Avoids231 α)) ×ˢ
      (Finset.univ.filter (fun β : Equiv.Perm (Fin b) => Avoids231 β))).filter
      (fun p =>
        peakCount p.1 + peakCount p.2 + (if a = 0 ∨ b = 0 then 0 else 1) = k)).card := by
  subst hab
  symm
  refine Finset.card_bij (fun (p : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) _ =>
    joinMax p.1 p.2) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    obtain ⟨⟨hα, hβ⟩, hpk⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (avoids231_joinMax_iff p.1 p.2).mpr ⟨hα, hβ⟩
    · rw [peakCount_joinMax]
      exact hpk
    · have h := joinMax_symm_last p.1 p.2
      have hv : ((joinMax p.1 p.2).symm (Fin.last (a + b))).val = a :=
        congrArg Fin.val h
      exact hv
  · intro p1 hp1 p2 hp2 heq
    have heq' : joinMax p1.1 p1.2 = joinMax p2.1 p2.2 := heq
    have h := joinMax_inj heq'
    exact Prod.ext h.1 h.2
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨⟨hAv, hpk⟩, hmax⟩ := hσ
    obtain ⟨α, β, rfl⟩ := exists_joinMax_eq σ hAv hmax
    have hAB := (avoids231_joinMax_iff α β).mp hAv
    refine ⟨(α, β), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    refine ⟨hAB, ?_⟩
    rw [peakCount_joinMax α β] at hpk
    exact hpk

private theorem avoidCount_succ (n k : ℕ) :
    avoidCount (n + 1) k = peakRec avoidCount n k := by
  have hmaps : Set.MapsTo (fun σ : Equiv.Perm (Fin (n + 1)) => (σ.symm (Fin.last n)).val)
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
        Avoids231 σ ∧ peakCount σ = k)) : Set (Equiv.Perm (Fin (n + 1))))
      (Finset.range n.succ) := by
    intro σ _
    apply Finset.mem_coe.mpr
    exact Finset.mem_range.mpr (σ.symm (Fin.last n)).isLt
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  have hav : ∀ (m j : ℕ),
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => Avoids231 σ)).filter
        (fun x => peakCount x = j)).card = avoidCount m j := by
    intro m j
    have hfl : (Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => Avoids231 σ)).filter
        (fun x => peakCount x = j) =
        Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => Avoids231 σ ∧ peakCount σ = j) := by
      rw [Finset.filter_filter]
    rw [hfl]
    rfl
  have hstep : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
        Avoids231 σ ∧ peakCount σ = k)).filter
        (fun σ => (σ.symm (Fin.last n)).val = q.1)).card =
      (if q.1 = 0 ∨ q.2 = 0 then peakConv avoidCount q.1 q.2 k
        else (if k = 0 then 0 else peakConv avoidCount q.1 q.2 (k - 1))) := by
    intro q hq
    have hmem : q.1 + q.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
    have hN7 := card_fiber_joinMax (a := q.1) (b := q.2) (n := n) (k := k) hmem
    have hbridge : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
          Avoids231 σ ∧ peakCount σ = k)).filter
          (fun σ => (σ.symm (Fin.last n)).val = q.1)).card =
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
          ((Avoids231 σ ∧ peakCount σ = k) ∧ (σ.symm (Fin.last n)).val = q.1))).card := by
      apply congrArg Finset.card
      rw [Finset.filter_filter]
    rw [hbridge, hN7]
    by_cases he : q.1 = 0 ∨ q.2 = 0
    · have hif : (if q.1 = 0 ∨ q.2 = 0 then peakConv avoidCount q.1 q.2 k
          else (if k = 0 then 0 else peakConv avoidCount q.1 q.2 (k - 1))) =
          peakConv avoidCount q.1 q.2 k := ite_eq_left he
      rw [hif]
      have hoff : (if q.1 = 0 ∨ q.2 = 0 then (0:ℕ) else 1) = 0 := ite_eq_left he
      have hfc : (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 +
              (if q.1 = 0 ∨ q.2 = 0 then 0 else 1) = k)) =
          (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 = k)) := by
        apply Finset.filter_congr
        intro p _
        simp only [hoff, add_zero]
      rw [hfc]
      have hN8 := card_filter_add_eq_sum_antidiagonal
        (Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α))
        (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))
        peakCount peakCount k
      rw [hN8]
      unfold peakConv
      apply Finset.sum_congr rfl
      intro r hr
      rw [hav q.1 r.1, hav q.2 r.2]
    · have hif : (if q.1 = 0 ∨ q.2 = 0 then peakConv avoidCount q.1 q.2 k
          else (if k = 0 then 0 else peakConv avoidCount q.1 q.2 (k - 1))) =
          (if k = 0 then 0 else peakConv avoidCount q.1 q.2 (k - 1)) :=
        ite_eq_right he
      rw [hif]
      have hoff : (if q.1 = 0 ∨ q.2 = 0 then (0:ℕ) else 1) = 1 := ite_eq_right he
      by_cases hk : k = 0
      · subst hk
        have hempty : (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 +
              (if q.1 = 0 ∨ q.2 = 0 then 0 else 1) = 0)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro p _
          omega
        rw [hempty, Finset.card_empty]
        exact (ite_eq_left rfl).symm
      · have hkif : (if k = 0 then (0:ℕ) else peakConv avoidCount q.1 q.2 (k - 1)) =
            peakConv avoidCount q.1 q.2 (k - 1) := ite_eq_right hk
        rw [hkif]
        have hfc : (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 +
              (if q.1 = 0 ∨ q.2 = 0 then 0 else 1) = k)) =
          (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 = k - 1)) := by
          apply Finset.filter_congr
          intro p _
          simp only [hoff]
          constructor <;> intro h <;> omega
        rw [hfc]
        have hN8 := card_filter_add_eq_sum_antidiagonal
          (Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α))
          (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))
          peakCount peakCount (k - 1)
        rw [hN8]
        unfold peakConv
        apply Finset.sum_congr rfl
        intro r hr
        rw [hav q.1 r.1, hav q.2 r.2]
  conv_lhs => unfold avoidCount
  rw [hfib, sum_range_fiber_eq_sum_antidiagonal]
  unfold peakRec
  apply Finset.sum_congr rfl
  intro q hq
  exact hstep q hq

-- N14
private theorem avoidCount_eq_peakT (n k : ℕ) : avoidCount n k = peakT n k := by
  revert k
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    by_cases hn : n = 0
    · subst hn
      have hA : ∀ σ : Equiv.Perm (Fin 0), Avoids231 σ := by
        intro σ i j l _ _ _
        exact Fin.elim0 i
      have hpc : ∀ σ : Equiv.Perm (Fin 0), peakCount σ = 0 := by
        intro σ
        unfold peakCount
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro x hx
        exact Fin.elim0 x
      have hset : (Finset.univ.filter
          (fun σ : Equiv.Perm (Fin 0) => Avoids231 σ ∧ peakCount σ = k)) =
          (if k = 0 then Finset.univ else ∅) := by
        ext σ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hk : k = 0
        · subst hk
          simp only [ite_true, Finset.mem_univ]
          rw [hpc σ]
          exact iff_true_intro ⟨hA σ, rfl⟩
        · have hk0 : peakCount σ ≠ k := by rw [hpc σ]; omega
          simp only [hk, ite_false, Finset.notMem_empty]
          exact iff_false_intro (fun h => hk0 h.2)
      have hcard : avoidCount 0 k = (if k = 0 then 1 else 0) := by
        unfold avoidCount
        rw [hset]
        by_cases hk : k = 0
        · subst hk
          simp only [ite_true, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, Nat.factorial_zero]
        · simp only [hk, ite_false, Finset.card_empty]
      have hT : peakT 0 k = (if k = 0 then 1 else 0) := by
        unfold peakT
        by_cases hk : k = 0
        · subst hk
          simp
        · have hC : Nat.choose (0 - 1) (2 * k) = 0 := by
            have h1 : (0:ℕ) - 1 = 0 := by omega
            rw [h1]
            apply Nat.choose_eq_zero_of_lt
            omega
          rw [hC]
          simp only [mul_zero, zero_mul, hk, ite_false]
      rw [hcard, hT]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hEq : ∀ a : ℕ, a ≤ m → ∀ j : ℕ, avoidCount a j = peakT a j := by
        intro a ha j
        exact ih a (by omega) j
      rw [avoidCount_succ, peakT_succ]
      unfold peakRec peakConv
      apply Finset.sum_congr rfl
      intro q hq
      have hmem : q.1 + q.2 = m :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      have ha1 : q.1 ≤ m := by omega
      have ha2 : q.2 ≤ m := by omega
      by_cases he : q.1 = 0 ∨ q.2 = 0
      · simp only [he, ite_true]
        apply Finset.sum_congr rfl
        intro p _
        rw [hEq q.1 ha1, hEq q.2 ha2]
      · simp only [he, ite_false]
        by_cases hk : k = 0
        · simp only [hk, ite_true]
        · simp only [hk, ite_false]
          apply Finset.sum_congr rfl
          intro p _
          rw [hEq q.1 ha1, hEq q.2 ha2]

end Peak231

-- N15
/--
The number of 231-avoiding permutations of length `n` with exactly `k` peaks has the stated
closed form.
Source: Lara Pudwell, Jacob Roth, and Teresa Wheeland, "Distributions of Statistics
over Pattern-Avoiding Permutations", Journal of Integer Sequences 22 (2019),
Article 19.2.6, Theorem `T:pk231`, line 228,
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Pudwell/pudwell6.tex>.

Proves `Wanted` entry `card_permutations_avoiding_231_with_peak_count`.
-/
theorem card_permutations_avoiding_231_with_peak_count
    (n k : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (∀ i j l : Fin n, i < j → j < l → ¬ (σ l < σ i ∧ σ i < σ j)) ∧
      (Finset.univ.filter (fun i : Fin n =>
        ∃ iPrev iNext : Fin n,
          iPrev.val + 1 = i.val ∧ i.val + 1 = iNext.val ∧
          σ iPrev < σ i ∧ σ iNext < σ i)).card = k)).card =
      2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) * Nat.choose (2 * k) k /
        (k + 1) := by
  have _ : 1 ≤ n := hn
  have hCat : (k + 1) * catalan k = Nat.choose (2 * k) k := by
    rw [succ_mul_catalan_eq_centralBinom, Nat.centralBinom_eq_two_mul_choose]
  have hRHS : 2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) *
      Nat.choose (2 * k) k / (k + 1) =
      2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) * catalan k := by
    have hC : Nat.choose (2 * k) k = (k + 1) * catalan k := hCat.symm
    conv_lhs => rw [hC]
    have hring : 2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) *
        ((k + 1) * catalan k) =
        (2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) * catalan k) *
        (k + 1) := by ring
    rw [hring, Nat.mul_div_cancel _ (Nat.succ_pos k)]
  have hBridge : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (∀ i j l : Fin n, i < j → j < l → ¬ (σ l < σ i ∧ σ i < σ j)) ∧
      (Finset.univ.filter (fun i : Fin n =>
        ∃ iPrev iNext : Fin n,
          iPrev.val + 1 = i.val ∧ i.val + 1 = iNext.val ∧
          σ iPrev < σ i ∧ σ iNext < σ i)).card = k)).card =
      Peak231.avoidCount n k := rfl
  rw [hBridge, Peak231.avoidCount_eq_peakT]
  unfold Peak231.peakT
  exact hRHS.symm

end MetaMathlibExt
end
