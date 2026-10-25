/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Def.Algebra.Lie.WittMultigradedValue
import Def.Combinatorics.Words.PrimitiveWord
import Mathlib.Data.List.Rotate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.List.PeriodicityLemma
import Def.Combinatorics.Words.LyndonWord.Part7
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

theorem length_wittRoot {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : (wittRoot w hw).length = wittPeriod w hw := by
  simp [wittRoot, wittPeriod_le_length]

theorem wittExponent_pos {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : 0 < wittExponent w hw := by
  apply Nat.div_pos (wittPeriod_le_length w hw)
  exact wittPeriod_pos w hw

theorem wittPeriod_mul_exponent {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) :
    wittPeriod w hw * wittExponent w hw = w.length := by
  exact Nat.mul_div_cancel' (wittPeriod_dvd_length w hw)

theorem wittWord_eq_root_power {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : w = wittWordPower (wittRoot w hw) (wittExponent w hw) := by
  apply wittEq_wordPower_take_of_hasPeriod
  · exact wittPeriod_pos w hw
  · exact wittExponent_pos w hw
  · exact (wittPeriod_mul_exponent w hw).symm
  · exact wittHasPeriod_of_rotate_eq (wittPeriod_le_length w hw)
      (wittRotate_period w hw)

theorem wittRotate_injective_of_period_eq_length {α : Type*} [DecidableEq α]
    {w : List α} (hw : w ≠ []) (hperiod : wittPeriod w hw = w.length)
    {i j : ℕ} (hi : i < w.length) (hj : j < w.length)
    (hrotate : w.rotate i = w.rotate j) : i = j := by
  have aux : ∀ {a b : ℕ}, a < b → b < w.length →
      w.rotate a = w.rotate b → False := by
    intro a b hab hb hrot
    have ha : a ≤ w.length := (hab.trans hb).le
    have heq₁ : a + (w.length - a) = w.length := Nat.add_sub_of_le ha
    have heq₂ : b + (w.length - a) = w.length + (b - a) := by omega
    have hfix : w.rotate (b - a) = w := by
      calc
        w.rotate (b - a) = (w.rotate w.length).rotate (b - a) := by
          rw [w.rotate_length]
        _ = w.rotate (w.length + (b - a)) := w.rotate_rotate _ _
        _ = w.rotate (b + (w.length - a)) := by rw [heq₂]
        _ = (w.rotate b).rotate (w.length - a) := (w.rotate_rotate _ _).symm
        _ = (w.rotate a).rotate (w.length - a) := by rw [hrot]
        _ = w.rotate (a + (w.length - a)) := w.rotate_rotate _ _
        _ = w := by rw [heq₁, w.rotate_length]
    have hle := wittPeriod_min w hw (q := b - a) (by omega) hfix
    rw [hperiod] at hle
    omega
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact aux hij hj hrotate
  · exact aux hji hi hrotate.symm

theorem wittWordPower_succ {α : Type*} (u : List α) (d : ℕ) :
    wittWordPower u (d + 1) = u ++ wittWordPower u d := by
  simp [wittWordPower, List.replicate_succ]

theorem wittWordPower_add {α : Type*} (u : List α) (a b : ℕ) :
    wittWordPower u (a + b) = wittWordPower u a ++ wittWordPower u b := by
  rw [wittWordPower, List.replicate_add, List.flatten_append]
  rfl

theorem wittWordPower_append_self {α : Type*} (u : List α) (d : ℕ) :
    wittWordPower u d ++ u = u ++ wittWordPower u d := by
  induction d with
  | zero => simp [wittWordPower]
  | succ d ih =>
      rw [wittWordPower_succ]
      simp only [List.append_assoc]
      rw [ih]

theorem wittRotate_length_power {α : Type*} (u : List α) (d : ℕ) :
    (wittWordPower u d).rotate u.length = wittWordPower u d := by
  cases d with
  | zero => simp [wittWordPower]
  | succ d =>
      rw [wittWordPower_succ, List.rotate_append_length_eq]
      exact wittWordPower_append_self u d

theorem wittIsPrimitiveWord_iff_period_eq_length {α : Type*} [DecidableEq α]
    {w : List α} (hw : w ≠ []) :
    IsPrimitiveWord w ↔ wittPeriod w hw = w.length := by
  constructor
  · intro hprimitive
    have hexponent : wittExponent w hw = 1 :=
      hprimitive.2 (wittRoot w hw) (wittExponent w hw)
        (wittWord_eq_root_power w hw).symm
    calc
      wittPeriod w hw = wittPeriod w hw * wittExponent w hw := by
        rw [hexponent, mul_one]
      _ = w.length := wittPeriod_mul_exponent w hw
  · intro hperiod
    refine ⟨hw, ?_⟩
    intro v n hpower
    change wittWordPower v n = w at hpower
    have hn : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      apply hw
      simpa [wittWordPower] using hpower.symm
    have hv : v ≠ [] := by
      intro hv
      subst v
      apply hw
      simpa [wittWordPower] using hpower.symm
    have hvpos : 0 < v.length := List.length_pos_of_ne_nil hv
    have hrot : w.rotate v.length = w := by
      rw [← hpower]
      exact wittRotate_length_power v n
    have hle := wittPeriod_min w hw hvpos hrot
    rw [hperiod] at hle
    have hlength := congr_arg List.length hpower
    rw [length_wittWordPower] at hlength
    by_contra hn1
    have hn2 : 2 ≤ n := by omega
    have hmul : 2 * v.length ≤ n * v.length := Nat.mul_le_mul_right v.length hn2
    rw [hlength] at hmul
    omega

theorem wittRotate_ne_of_nodup_cyclicPermutations {α : Type*} {w : List α}
    (hw0 : w ≠ []) (hw : w.cyclicPermutations.Nodup) {k : ℕ}
    (hk0 : 0 < k) (hk : k < w.length) : w.rotate k ≠ w := by
  intro hrotate
  have hlen := List.length_cyclicPermutations_of_ne_nil w hw0
  let i : Fin w.cyclicPermutations.length := ⟨0, by rw [hlen]; omega⟩
  let j : Fin w.cyclicPermutations.length := ⟨k, by rw [hlen]; exact hk⟩
  have hget : w.cyclicPermutations.get i = w.cyclicPermutations.get j := by
    rw [List.get_cyclicPermutations, List.get_cyclicPermutations]
    simpa [i, j] using hrotate.symm
  have hij := List.nodup_iff_injective_get.mp hw hget
  have hval := congr_arg Fin.val hij
  simp [i, j] at hval
  omega

/-- A nonempty finite word is primitive if and only if its cyclic permutations are distinct. -/
theorem isPrimitiveWord_iff_nodup_cyclicPermutations {α : Type*} {w : List α} :
    IsPrimitiveWord w ↔ w ≠ [] ∧ w.cyclicPermutations.Nodup := by
  classical
  constructor
  · intro hw
    refine ⟨hw.1, List.nodup_iff_injective_get.mpr ?_⟩
    intro i j hget
    apply Fin.ext
    apply wittRotate_injective_of_period_eq_length hw.1
      ((wittIsPrimitiveWord_iff_period_eq_length hw.1).mp hw)
    · rw [← List.length_cyclicPermutations_of_ne_nil w hw.1]
      exact i.2
    · rw [← List.length_cyclicPermutations_of_ne_nil w hw.1]
      exact j.2
    · simpa only [List.get_cyclicPermutations] using hget
  · rintro ⟨hw0, hw⟩
    apply (wittIsPrimitiveWord_iff_period_eq_length hw0).2
    apply le_antisymm (wittPeriod_le_length w hw0)
    by_contra hnot
    have hlt : wittPeriod w hw0 < w.length := Nat.lt_of_not_ge hnot
    exact wittRotate_ne_of_nodup_cyclicPermutations hw0 hw
      (wittPeriod_pos w hw0) hlt (wittRotate_period w hw0)

/-- A primitive word is changed by every nontrivial rotation. -/
theorem rotate_ne_of_isPrimitiveWord {α : Type*} {w : List α}
    (hw : IsPrimitiveWord w) {k : ℕ} (hk0 : 0 < k) (hk : k < w.length) :
    w.rotate k ≠ w := by
  exact wittRotate_ne_of_nodup_cyclicPermutations hw.1
    (isPrimitiveWord_iff_nodup_cyclicPermutations.mp hw).2 hk0 hk

theorem wittWordPower_power {α : Type*} (u : List α) (e d : ℕ) :
    wittWordPower (wittWordPower u e) d = wittWordPower u (d * e) := by
  induction d with
  | zero => simp [wittWordPower]
  | succ d ih =>
      rw [wittWordPower_succ, ih, ← wittWordPower_add]
      congr 1
      simp [Nat.add_mul, add_comm]

theorem wittWordPower_eq_ofFn {α : Type*} (u : List α) (d : ℕ) :
    wittWordPower u d = List.ofFn (Fin.repeat d u.get) := by
  rw [List.ofFn_fin_repeat, List.ofFn_get]
  rfl

theorem wittGetElem_power {α : Type*} {u : List α} {d i : ℕ}
    (hu : u ≠ []) (hi : i < (wittWordPower u d).length) :
    (wittWordPower u d)[i] =
      u[i % u.length]'(Nat.mod_lt i (List.length_pos_of_ne_nil hu)) := by
  have heq := congr_arg (fun z : List α => z[i]?) (wittWordPower_eq_ofFn u d)
  have hifn : i < (List.ofFn (Fin.repeat d u.get)).length := by
    simpa [length_wittWordPower] using hi
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hifn,
    List.getElem_ofFn, Fin.repeat_apply] at heq
  have hval := Option.some.inj heq
  calc
    (wittWordPower u d)[i] = u.get _ := hval
    _ = u[i % u.length]'(Nat.mod_lt i (List.length_pos_of_ne_nil hu)) := by
      apply congr_arg u.get
      apply Fin.ext
      simp [Fin.modNat]

theorem wittRotate_eq_of_power_rotate_eq {α : Type*} {u : List α}
    (hu : u ≠ []) {d q : ℕ} (hd : 0 < d)
    (hrotate : (wittWordPower u d).rotate q = wittWordPower u d) :
    u.rotate q = u := by
  let W := wittWordPower u d
  have hlen : W.length = d * u.length := length_wittWordPower u d
  have hpW : u.length ≤ W.length := by
    rw [hlen]
    exact Nat.le_mul_of_pos_left u.length hd
  have hpdvd : u.length ∣ W.length := by
    rw [hlen]
    exact ⟨d, by simp [mul_comm]⟩
  have hWpos : 0 < W.length := by
    rw [hlen]
    exact Nat.mul_pos hd (List.length_pos_of_ne_nil hu)
  apply List.ext_getElem
  · simp
  · intro i hirot hiu
    have hi : i < u.length := hiu
    have hiW : i < W.length := hi.trans_le hpW
    have hiWr : i < (W.rotate q).length := by simpa using hiW
    have hopt := congr_arg (fun z : List α => z[i]?) hrotate
    rw [List.getElem?_eq_getElem hiWr, List.getElem?_eq_getElem hiW] at hopt
    have hval := Option.some.inj hopt
    rw [List.getElem_rotate] at hval
    have hleft := wittGetElem_power hu
      (Nat.mod_lt (i + q) hWpos :
        (i + q) % W.length < (wittWordPower u d).length)
    have hright := wittGetElem_power hu hiW
    rw [hleft, hright] at hval
    rw [List.getElem_rotate]
    simpa only [Nat.mod_mod_of_dvd (i + q) hpdvd, Nat.mod_eq_of_lt hi] using hval

theorem wittWordPower_ne_nil {α : Type*} {u : List α} (hu : u ≠ [])
    {d : ℕ} (hd : 0 < d) : wittWordPower u d ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [length_wittWordPower]
  exact Nat.mul_pos hd (List.length_pos_of_ne_nil hu)

theorem wittPeriod_power_of_primitive {α : Type*} [DecidableEq α]
    {u : List α} (hu : IsPrimitiveWord u) {d : ℕ} (hd : 0 < d) :
    wittPeriod (wittWordPower u d) (wittWordPower_ne_nil hu.1 hd) = u.length := by
  let W := wittWordPower u d
  let hW : W ≠ [] := wittWordPower_ne_nil hu.1 hd
  apply le_antisymm
  · apply wittPeriod_min W hW (List.length_pos_of_ne_nil hu.1)
    exact wittRotate_length_power u d
  · by_contra hnot
    have hlt : wittPeriod W hW < u.length := Nat.lt_of_not_ge hnot
    have hrootrotate : u.rotate (wittPeriod W hW) = u :=
      wittRotate_eq_of_power_rotate_eq hu.1 hd (wittRotate_period W hW)
    exact rotate_ne_of_isPrimitiveWord hu (wittPeriod_pos W hW) hlt hrootrotate

theorem wittTake_length_power {α : Type*} (u : List α) {d : ℕ} (hd : 0 < d) :
    (wittWordPower u d).take u.length = u := by
  cases d with
  | zero => omega
  | succ d =>
      rw [wittWordPower_succ]
      simp

theorem wittRoot_power_of_primitive {α : Type*} [DecidableEq α]
    {u : List α} (hu : IsPrimitiveWord u) {d : ℕ} (hd : 0 < d) :
    wittRoot (wittWordPower u d) (wittWordPower_ne_nil hu.1 hd) = u := by
  rw [wittRoot, wittPeriod_power_of_primitive hu hd]
  exact wittTake_length_power u hd

theorem wittExponent_power_of_primitive {α : Type*} [DecidableEq α]
    {u : List α} (hu : IsPrimitiveWord u) {d : ℕ} (hd : 0 < d) :
    wittExponent (wittWordPower u d) (wittWordPower_ne_nil hu.1 hd) = d := by
  rw [wittExponent, wittPeriod_power_of_primitive hu hd, length_wittWordPower]
  exact Nat.mul_div_left d (List.length_pos_of_ne_nil hu.1)

theorem wittRoot_isPrimitive {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : IsPrimitiveWord (wittRoot w hw) := by
  let u := wittRoot w hw
  have hu : u ≠ [] := by
    apply List.ne_nil_of_length_pos
    dsimp [u]
    rw [length_wittRoot]
    exact wittPeriod_pos w hw
  let q := wittPeriod u hu
  let v := wittRoot u hu
  let e := wittExponent u hu
  let d := wittExponent w hw
  have hudecomp : u = wittWordPower v e := by
    exact wittWord_eq_root_power u hu
  have hpowerfix : (wittWordPower u d).rotate q = wittWordPower u d := by
    calc
      (wittWordPower u d).rotate q =
          (wittWordPower (wittWordPower v e) d).rotate q :=
        congr_arg (fun z => (wittWordPower z d).rotate q) hudecomp
      _ = (wittWordPower v (d * e)).rotate q :=
        congr_arg (fun z => z.rotate q) (wittWordPower_power v e d)
      _ = wittWordPower v (d * e) := by
        rw [show q = v.length by
          dsimp [q, v]
          exact (length_wittRoot u hu).symm]
        exact wittRotate_length_power v (d * e)
      _ = wittWordPower (wittWordPower v e) d := (wittWordPower_power v e d).symm
      _ = wittWordPower u d :=
        congr_arg (fun z => wittWordPower z d) hudecomp.symm
  have hwdecomp : w = wittWordPower u d := wittWord_eq_root_power w hw
  have hfix : w.rotate q = w := by
    calc
      w.rotate q = (wittWordPower u d).rotate q := congr_arg (fun z => z.rotate q) hwdecomp
      _ = wittWordPower u d := hpowerfix
      _ = w := hwdecomp.symm
  change IsPrimitiveWord u
  apply (wittIsPrimitiveWord_iff_period_eq_length hu).2
  apply le_antisymm (wittPeriod_le_length u hu)
  have hle : wittPeriod w hw ≤ q :=
    wittPeriod_min w hw (wittPeriod_pos u hu) hfix
  calc
    u.length = wittPeriod w hw := by
      dsimp [u]
      exact length_wittRoot w hw
    _ ≤ q := hle

end MetaMathlibExt
