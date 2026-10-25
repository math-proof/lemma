/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Sym.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Fintype.Fin
import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part3


section

namespace MetaMathlibExt

theorem shiftFwd_mono {m K x : ℕ} {w : Fin K → Fin m}
    {e : Fin K → Fin x} {hmono : IsMono w e} :
    Monotone (shiftFwd w e hmono) := by
  intro a b hab
  have hab' : a.val ≤ b.val := Fin.le_iff_val_le_val.mp hab
  have ha' : a.val < K := a.isLt
  have hb' : b.val < K := b.isLt
  have hleap := mono_leap hmono a.val b.val hab' hb' ha'
  have hlow_a : desPrefix w a.val ≤ (e a).val :=
    mono_lower hmono a.val ha'
  have hlow_b : desPrefix w b.val ≤ (e b).val :=
    mono_lower hmono b.val hb'
  have hle_s : desPrefix w a.val ≤ desPrefix w b.val :=
    (desPrefix_mono w) hab'
  have heq_a : (e ⟨a.val, ha'⟩).val = (e a).val := rfl
  have heq_b : (e ⟨b.val, hb'⟩).val = (e b).val := rfl
  rw [Fin.le_iff_val_le_val]
  change (e a).val - desPrefix w a.val ≤
    (e b).val - desPrefix w b.val
  omega

theorem shiftBwd_monotone {m K x : ℕ} (w : Fin K → Fin m)
    (g : Fin K → Fin (x - desPrefix w K)) (hg : Monotone g) :
    Monotone (shiftBwd w g) := by
  intro a b hab
  by_cases hle : desPrefix w K ≤ x
  · have hab' : a.val ≤ b.val := Fin.le_iff_val_le_val.mp hab
    have hg_le : g a ≤ g b := hg hab
    have hg_val : (g a).val ≤ (g b).val :=
      Fin.le_iff_val_le_val.mp hg_le
    have hs_le : desPrefix w a.val ≤ desPrefix w b.val :=
      (desPrefix_mono w) hab'
    unfold shiftBwd
    simp only [hle, dite_true]
    rw [Fin.le_iff_val_le_val]
    change (g a).val + desPrefix w a.val ≤
      (g b).val + desPrefix w b.val
    omega
  · have hx : x ≤ desPrefix w K := by omega
    have h0 : x - desPrefix w K = 0 :=
      Nat.sub_eq_zero_of_le hx
    have hfalse : False := Fin.elim0 (h0 ▸ g a)
    exact False.elim hfalse

theorem shiftBwd_strict {m K x : ℕ} (w : Fin K → Fin m)
    (g : Fin K → Fin (x - desPrefix w K)) (hg : Monotone g)
    (j : Fin K) (h : j.val + 1 < K)
    (hw : w j > w ⟨j.val + 1, h⟩) :
    shiftBwd w g j < shiftBwd w g ⟨j.val + 1, h⟩ := by
  by_cases hle : desPrefix w K ≤ x
  · have hj_le : j ≤ ⟨j.val + 1, h⟩ := by
      change j.val ≤ j.val + 1
      omega
    have hg_le : g j ≤ g ⟨j.val + 1, h⟩ := hg hj_le
    have hg_val : (g j).val ≤ (g ⟨j.val + 1, h⟩).val :=
      Fin.le_iff_val_le_val.mp hg_le
    have hw' : w ⟨j.val, by omega⟩ > w ⟨j.val + 1, h⟩ := hw
    have hdes1 : desInd w j.val = 1 := by
      unfold desInd
      simp only [h, dite_true, hw', ite_true]
    have hsucc : desPrefix w (j.val + 1) =
        desPrefix w j.val + 1 := by
      rw [desPrefix_succ, hdes1]
    unfold shiftBwd
    simp only [hle, dite_true]
    rw [Fin.lt_def]
    change (g j).val + desPrefix w j.val <
      (g ⟨j.val + 1, h⟩).val + desPrefix w (j.val + 1)
    omega
  · have hx : x ≤ desPrefix w K := by omega
    have h0 : x - desPrefix w K = 0 :=
      Nat.sub_eq_zero_of_le hx
    have hfalse : False := Fin.elim0 (h0 ▸ g j)
    exact False.elim hfalse

theorem mono_des_le {m K x : ℕ} {w : Fin K → Fin m}
    {e : Fin K → Fin x} (hmono : IsMono w e) :
    desPrefix w K ≤ x := by
  by_cases hK : K = 0
  · subst hK
    rw [desPrefix_zero]
    exact Nat.zero_le _
  · have hKpos : 0 < K := by omega
    have hup := mono_upper hmono 0 hKpos
    have hz : desPrefix w 0 = 0 := desPrefix_zero w
    omega

theorem shiftBwd_isMono {m K x : ℕ} (w : Fin K → Fin m)
    (g : Fin K → Fin (x - desPrefix w K)) (hg : Monotone g) :
    IsMono w (shiftBwd w g) := by
  constructor
  · exact shiftBwd_monotone w g hg
  · intro j h hw
    exact shiftBwd_strict w g hg j h hw

theorem shiftFwdBwd {m K x : ℕ} (w : Fin K → Fin m)
    (e : Fin K → Fin x) (hmono : IsMono w e) :
    shiftBwd w (shiftFwd w e hmono) = e := by
  have hle : desPrefix w K ≤ x := mono_des_le hmono
  funext j
  have hn : j.val < K := j.isLt
  have hlow : desPrefix w j.val ≤ (e j).val :=
    mono_lower hmono j.val hn
  have hg_val : ((shiftFwd w e hmono) j).val =
      (e j).val - desPrefix w j.val := rfl
  have h1g : ((shiftFwd w e hmono) j).val <
      x - desPrefix w K :=
    ((shiftFwd w e hmono) j).isLt
  have h2s : desPrefix w j.val ≤ desPrefix w K :=
    desPrefix_le_total w j.val (by omega)
  have he_eq : shiftBwd w (shiftFwd w e hmono) j =
      ⟨((shiftFwd w e hmono) j).val + desPrefix w j.val,
        by omega⟩ := by
    unfold shiftBwd
    simp only [hle, dite_true]
  apply Fin.ext
  simp only [he_eq, hg_val]
  exact Nat.sub_add_cancel hlow

theorem shiftBwdFwd {m K x : ℕ} (w : Fin K → Fin m)
    (g : Fin K → Fin (x - desPrefix w K)) (hg : Monotone g) :
    shiftFwd w (shiftBwd w g)
        (shiftBwd_isMono w g hg) = g := by
  by_cases hle : desPrefix w K ≤ x
  · funext j
    have he_val : ((shiftBwd w g) j).val =
        (g j).val + desPrefix w j.val := by
      unfold shiftBwd
      simp only [hle, dite_true]
    have hg_val : ((shiftFwd w (shiftBwd w g)
        (shiftBwd_isMono w g hg)) j).val =
        ((shiftBwd w g) j).val - desPrefix w j.val := rfl
    apply Fin.ext
    simp only [hg_val, he_val]
    exact Nat.add_sub_cancel _ _
  · have hx : x ≤ desPrefix w K := by omega
    have h0 : x - desPrefix w K = 0 :=
      Nat.sub_eq_zero_of_le hx
    funext j
    have hfalse : False := Fin.elim0 (h0 ▸ g j)
    exact False.elim hfalse

end MetaMathlibExt
end
