/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Dimension.Finite
import Def.Algebra.Lie.FreeLieMultihomogeneousComponent
import Def.Algebra.Lie.WittMultigradedValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Rotate
import Theorem.Combinatorics.Words.LyndonWord.Part14
import Lemma.Finset.Words.LyndonWord
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeAlgebra
import Def.Algebra.Lie.WittMultigradedDimension.Part3
open scoped BigOperators

/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/


namespace MetaMathlibExt

theorem wittLongestLyndon_append {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) :
    w = wittLongestLyndonPrefix w hw ++ wittLongestLyndonSuffix w hw := by
  exact (List.take_append_drop (wittLongestLyndonSuffixIndex w hw) w).symm

theorem wittLongestLyndonPrefix_ne_nil {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) : wittLongestLyndonPrefix w hw ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [wittLongestLyndonPrefix, List.length_take,
    min_eq_left (wittLongestLyndonSuffixIndex_spec w hw).2.1.le]
  exact (wittLongestLyndonSuffixIndex_spec w hw).1

theorem wittLongestLyndonSuffix_ne_nil {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) : wittLongestLyndonSuffix w hw ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [wittLongestLyndonSuffix, List.length_drop]
  have hk := (wittLongestLyndonSuffixIndex_spec w hw).2.1
  omega

theorem wittLongestLyndonSuffix_isLyndon {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) :
    WittSuffixLyndon (wittLongestLyndonSuffix w hw) :=
  (wittLongestLyndonSuffixIndex_spec w hw).2.2

theorem length_wittLongestLyndonPrefix {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) :
    (wittLongestLyndonPrefix w hw).length = wittLongestLyndonSuffixIndex w hw := by
  rw [wittLongestLyndonPrefix, List.length_take,
    min_eq_left (wittLongestLyndonSuffixIndex_spec w hw).2.1.le]

theorem wittLongestLyndonPrefix_isLyndon_of_lt {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length)
    (hlt : w < wittLongestLyndonSuffix w hw) :
    WittSuffixLyndon (wittLongestLyndonPrefix w hw) := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      let u := wittLongestLyndonPrefix w hw
      let v := wittLongestLyndonSuffix w hw
      have huv : w = u ++ v := wittLongestLyndon_append w hw
      have hu_ne : u ≠ [] := wittLongestLyndonPrefix_ne_nil w hw
      have hv_ne : v ≠ [] := wittLongestLyndonSuffix_ne_nil w hw
      have hvL : WittSuffixLyndon v := wittLongestLyndonSuffix_isLyndon w hw
      have huv_lt : u ++ v < v := huv ▸ hlt
      have hu_lt_v : u < v := wittAppend_lt_right_imp_left_lt huv_lt
      change WittSuffixLyndon u
      by_cases hu1 : u.length = 1
      · obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hu1
        exact ha ▸ wittSuffixLyndon_singleton a
      · have hu2 : 2 ≤ u.length := by
          have hu0 := List.length_pos_of_ne_nil hu_ne
          omega
        let x := wittLongestLyndonPrefix u hu2
        let z := wittLongestLyndonSuffix u hu2
        have huxz : u = x ++ z := wittLongestLyndon_append u hu2
        have hx_ne : x ≠ [] := wittLongestLyndonPrefix_ne_nil u hu2
        have hz_ne : z ≠ [] := wittLongestLyndonSuffix_ne_nil u hu2
        have hzL : WittSuffixLyndon z := wittLongestLyndonSuffix_isLyndon u hu2
        have hvz : v ≤ z := by
          apply le_of_not_gt
          intro hzv
          have hzvL : WittSuffixLyndon (z ++ v) := wittSuffixLyndon_append hzL hvL hzv
          have hdrop : w.drop x.length = z ++ v := by
            rw [huv, huxz]
            simp [List.append_assoc]
          have hx0 : 0 < x.length := List.length_pos_of_ne_nil hx_ne
          have hxw : x.length < w.length := by
            have hz0 := List.length_pos_of_ne_nil hz_ne
            have hv0 := List.length_pos_of_ne_nil hv_ne
            simp only [huv, huxz, List.length_append]
            omega
          have hmin := wittLongestLyndonSuffixIndex_min w hw hx0 hxw (hdrop ▸ hzvL)
          have hku : wittLongestLyndonSuffixIndex w hw = u.length := by
            rw [← length_wittLongestLyndonPrefix w hw]
          have hxu : x.length < u.length := by
            have hz0 := List.length_pos_of_ne_nil hz_ne
            rw [huxz, List.length_append]
            omega
          omega
        have hu_lt_z : u < z := hu_lt_v.trans_le hvz
        have hxu : x < z := by
          have hxz_lt : x ++ z < z := huxz ▸ hu_lt_z
          exact wittAppend_lt_right_imp_left_lt hxz_lt
        have hxL : WittSuffixLyndon x := by
          apply ih u.length
          · calc
              u.length < (u ++ v).length := by
                rw [List.length_append]
                exact Nat.lt_add_of_pos_right (List.length_pos_of_ne_nil hv_ne)
              _ = w.length := congr_arg List.length huv.symm
              _ = n := hn
          · exact hu_lt_z
          · rfl
        have huL : WittSuffixLyndon (x ++ z) := wittSuffixLyndon_append hxL hzL hxu
        exact huxz ▸ huL

theorem wittStandardFactorization {α : Type*} [LinearOrder α]
    {w : List α} (hw : IsLyndonWord w) (hw2 : 2 ≤ w.length) :
    IsLyndonWord (wittLongestLyndonPrefix w hw2) ∧
      IsLyndonWord (wittLongestLyndonSuffix w hw2) ∧
      wittLongestLyndonPrefix w hw2 < wittLongestLyndonSuffix w hw2 := by
  have hwS := (wittLyndon_iff_suffix w).mp hw
  have hlt : w < wittLongestLyndonSuffix w hw2 :=
    hwS.2 _ _ (wittLongestLyndonPrefix_ne_nil w hw2)
      (wittLongestLyndonSuffix_ne_nil w hw2) (wittLongestLyndon_append w hw2)
  have hpS := wittLongestLyndonPrefix_isLyndon_of_lt w hw2 hlt
  have hsS := wittLongestLyndonSuffix_isLyndon w hw2
  refine ⟨(wittLyndon_iff_suffix _).mpr hpS, (wittLyndon_iff_suffix _).mpr hsS, ?_⟩
  have happ_lt : wittLongestLyndonPrefix w hw2 ++ wittLongestLyndonSuffix w hw2 <
      wittLongestLyndonSuffix w hw2 := (wittLongestLyndon_append w hw2) ▸ hlt
  exact wittAppend_lt_right_imp_left_lt happ_lt

end MetaMathlibExt
