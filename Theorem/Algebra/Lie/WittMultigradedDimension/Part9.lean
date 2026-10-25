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
import Def.Algebra.Lie.WittMultigradedDimension.Part8
open scoped BigOperators

/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/


namespace MetaMathlibExt

attribute [local instance 100] LieRing.ofAssociativeRing

theorem wittAssocLyndonFamily_linearIndependent (K : Type) [Field K] {r : ℕ}
    (degree : Fin r → ℕ) :
    LinearIndependent K (fun w : LyndonWordsOfContent degree =>
      wittAssocLift K (wittLyndonFamily K degree w)) := by
  classical
  let _ : LinearOrder (LyndonWordsOfContent degree) :=
    LinearOrder.lift' (fun w => w.1.1) fun _ _ h => Subtype.ext (Subtype.ext h)
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  by_contra hi
  let s := Finset.univ.filter fun j => g j ≠ 0
  have hs : s.Nonempty := ⟨i, by simp [s, hi]⟩
  let m := s.min' hs
  have hmne : g m ≠ 0 := by
    have hm := Finset.min'_mem s hs
    simpa [s] using hm
  have hbefore : ∀ j, j < m → g j = 0 := by
    intro j hjm
    by_contra hj
    have hjmem : j ∈ s := by simp [s, hj]
    exact (not_le_of_gt hjm) (Finset.min'_le s j hjmem)
  let coord : FreeAlgebra K (Fin r) →ₗ[K] K :=
    (Finsupp.lapply (R := K) (FreeMonoid.ofList m.1.1)).comp
      (FreeAlgebra.basisFreeMonoid K (Fin r)).repr.toLinearMap
  have hcoord :
      (∑ j, g j * (FreeAlgebra.basisFreeMonoid K (Fin r)).repr
        (wittAssocLift K (wittLyndonFamily K degree j)) (FreeMonoid.ofList m.1.1)) = 0 := by
    have h := congrArg coord hsum
    simpa [coord] using h
  have hsum_single :
      (∑ j, g j * (FreeAlgebra.basisFreeMonoid K (Fin r)).repr
        (wittAssocLift K (wittLyndonFamily K degree j)) (FreeMonoid.ofList m.1.1)) = g m := by
    calc
      _ = g m * (FreeAlgebra.basisFreeMonoid K (Fin r)).repr
          (wittAssocLift K (wittLyndonFamily K degree m)) (FreeMonoid.ofList m.1.1) :=
        Fintype.sum_eq_single m (by
          intro j hjm
          rcases lt_or_gt_of_ne hjm with hjlt | hmlt
          · rw [hbefore j hjlt, zero_mul]
          · have hmlt' : m.1.1 < j.1.1 := hmlt
            rw [wittLyndonFamily, wittTriangular_repr_eq_zero_of_lt K
              (wittAssocLift_lyndonBracket_triangular K j.1.1 j.2) hmlt', mul_zero])
      _ = g m := by
        rw [wittLyndonFamily,
          wittTriangular_repr_self K
            (wittAssocLift_lyndonBracket_triangular K m.1.1 m.2), mul_one]
  rw [hsum_single] at hcoord
  exact hmne hcoord

theorem wittLyndonFamily_linearIndependent (K : Type) [Field K] {r : ℕ}
    (degree : Fin r → ℕ) :
    LinearIndependent K (wittLyndonFamily K degree) := by
  apply LinearIndependent.of_comp (wittAssocLift K).toLinearMap
  exact wittAssocLyndonFamily_linearIndependent K degree

theorem wittExists_lyndonSuffix_le {α : Type*} [LinearOrder α]
    (w : List α) (hw : w ≠ []) :
    ∃ a s, s ≠ [] ∧ IsLyndonWord s ∧ w = a ++ s ∧ s ≤ w := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      by_cases hwL : IsLyndonWord w
      · exact ⟨[], w, hw, hwL, by simp, le_rfl⟩
      · have hnS : ¬WittSuffixLyndon w := by
          exact fun hS => hwL ((wittLyndon_iff_suffix w).mpr hS)
        have hnforall :
            ¬∀ a s, a ≠ [] → s ≠ [] → w = a ++ s → w < s := by
          exact fun h => hnS ⟨hw, h⟩
        push Not at hnforall
        obtain ⟨a, s, ha, hs, has, hws⟩ := hnforall
        have hslen : s.length < n := by
          have halen := List.length_pos_of_ne_nil ha
          rw [← hn, has, List.length_append]
          omega
        obtain ⟨b, t, ht, htL, hst, htle⟩ := ih s.length hslen s hs rfl
        refine ⟨a ++ b, t, ht, htL, ?_, htle.trans hws⟩
        rw [has, hst, List.append_assoc]

theorem wittLongestLyndonSuffix_le_suffix {α : Type*} [LinearOrder α]
    {w : List α} (_hw : IsLyndonWord w) (hw2 : 2 ≤ w.length)
    {a q : List α} (ha : a ≠ []) (hq : q ≠ []) (hwq : w = a ++ q) :
    wittLongestLyndonSuffix w hw2 ≤ q := by
  obtain ⟨b, s, hs, hsL, hqbs, hsle⟩ := wittExists_lyndonSuffix_le q hq
  let j := (a ++ b).length
  have hwabs : w = (a ++ b) ++ s := by rw [hwq, hqbs, List.append_assoc]
  have hj0 : 0 < j := by
    dsimp [j]
    have ha0 := List.length_pos_of_ne_nil ha
    simp only [List.length_append]
    omega
  have hjw : j < w.length := by
    have hs0 := List.length_pos_of_ne_nil hs
    rw [hwabs, List.length_append]
    dsimp [j]
    omega
  have hdrop : w.drop j = s := by
    rw [hwabs]
    simp [j]
  have hdropL : WittSuffixLyndon (w.drop j) := by
    rw [hdrop]
    exact (wittLyndon_iff_suffix s).mp hsL
  have hmin : wittLongestLyndonSuffixIndex w hw2 ≤ j :=
    wittLongestLyndonSuffixIndex_min w hw2 hj0 hjw hdropL
  let c := (a ++ b).drop (wittLongestLyndonSuffixIndex w hw2)
  have hvcs : wittLongestLyndonSuffix w hw2 = c ++ s := by
    unfold wittLongestLyndonSuffix
    calc
      w.drop (wittLongestLyndonSuffixIndex w hw2) =
          ((a ++ b) ++ s).drop (wittLongestLyndonSuffixIndex w hw2) :=
        congr_arg (List.drop (wittLongestLyndonSuffixIndex w hw2)) hwabs
      _ = c ++ s := by rw [List.drop_append_of_le_length hmin]
  have hvle : wittLongestLyndonSuffix w hw2 ≤ s := by
    by_cases hc : c = []
    · simp [hvcs, hc]
    · exact (wittLongestLyndonSuffix_isLyndon w hw2).2 c s hc hs hvcs |>.le
  exact hvle.trans hsle

theorem wittStandardFactorization_append {α : Type*} [LinearOrder α]
    {u v : List α} (hu : IsLyndonWord u) (hv : IsLyndonWord v) (_huv : u < v)
    (hu2 : 2 ≤ u.length)
    (hvu : v ≤ wittLongestLyndonSuffix u hu2) :
    let hw2 : 2 ≤ (u ++ v).length := by
      simp only [List.length_append]
      omega
    wittLongestLyndonPrefix (u ++ v) hw2 = u ∧
      wittLongestLyndonSuffix (u ++ v) hw2 = v := by
  dsimp only
  have hw2 : 2 ≤ (u ++ v).length := by
    simp only [List.length_append]
    omega
  let k := wittLongestLyndonSuffixIndex (u ++ v) hw2
  have huk : k ≤ u.length := by
    apply wittLongestLyndonSuffixIndex_min (u ++ v) hw2
    · exact List.length_pos_of_ne_nil hu.1
    · simp only [List.length_append]
      exact Nat.lt_add_of_pos_right (List.length_pos_of_ne_nil hv.1)
    · have hdrop : (u ++ v).drop u.length = v := by simp
      rw [hdrop]
      exact (wittLyndon_iff_suffix v).mp hv
  have hku : k = u.length := by
    apply le_antisymm huk
    by_contra hnot
    have hku_lt : k < u.length := Nat.lt_of_not_ge hnot
    let q := u.drop k
    have hq : q ≠ [] := by
      apply List.ne_nil_of_length_pos
      change (u.drop k).length > 0
      rw [List.length_drop]
      omega
    have hk0 : 0 < k := (wittLongestLyndonSuffixIndex_spec (u ++ v) hw2).1
    have ht : u.take k ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [List.length_take, min_eq_left hku_lt.le]
      exact hk0
    have hu_decomp : u = u.take k ++ q := by
      exact (List.take_append_drop k u).symm
    have hbq : wittLongestLyndonSuffix u hu2 ≤ q :=
      wittLongestLyndonSuffix_le_suffix hu hu2 ht hq hu_decomp
    have hsuffix : wittLongestLyndonSuffix (u ++ v) hw2 = q ++ v := by
      rw [wittLongestLyndonSuffix, show wittLongestLyndonSuffixIndex (u ++ v) hw2 = k from rfl,
        List.drop_append_of_le_length huk]
    have hltv : wittLongestLyndonSuffix (u ++ v) hw2 < v :=
      (wittLongestLyndonSuffix_isLyndon (u ++ v) hw2).2 q v hq hv.1 hsuffix
    have hqv : q < v := by
      rw [hsuffix] at hltv
      exact wittAppend_lt_right_imp_left_lt hltv
    exact (not_lt_of_ge (hvu.trans hbq)) hqv
  constructor
  · unfold wittLongestLyndonPrefix
    change (u ++ v).take k = u
    rw [hku]
    simp
  · unfold wittLongestLyndonSuffix
    change (u ++ v).drop k = v
    rw [hku]
    simp

theorem wittLyndonBracket_append (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} (hu : IsLyndonWord u) (hv : IsLyndonWord v) (_huv : u < v)
    (hu2 : 2 ≤ u.length)
    (hvu : v ≤ wittLongestLyndonSuffix u hu2) :
    wittLyndonBracket K (u ++ v)
        ((wittLyndon_iff_suffix (u ++ v)).mpr
          (wittSuffixLyndon_append ((wittLyndon_iff_suffix u).mp hu)
            ((wittLyndon_iff_suffix v).mp hv) _huv)) =
      ⁅wittLyndonBracket K u hu, wittLyndonBracket K v hv⁆ := by
  have hw2 : 2 ≤ (u ++ v).length := by
    simp only [List.length_append]
    omega
  have hfac := wittStandardFactorization_append hu hv _huv hu2 hvu
  rw [wittLyndonBracket]
  split_ifs with hlen
  · omega
  · simp only [hfac.1, hfac.2]

theorem wittLyndonBracket_append_of_length_one (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} (hu : IsLyndonWord u) (hv : IsLyndonWord v) (_huv : u < v)
    (hu1 : u.length = 1) :
    wittLyndonBracket K (u ++ v)
        ((wittLyndon_iff_suffix (u ++ v)).mpr
          (wittSuffixLyndon_append ((wittLyndon_iff_suffix u).mp hu)
            ((wittLyndon_iff_suffix v).mp hv) _huv)) =
      ⁅wittLyndonBracket K u hu, wittLyndonBracket K v hv⁆ := by
  have hw2 : 2 ≤ (u ++ v).length := by
    have hv0 := List.length_pos_of_ne_nil hv.1
    simp only [List.length_append]
    omega
  let k := wittLongestLyndonSuffixIndex (u ++ v) hw2
  have huk : k ≤ u.length := by
    apply wittLongestLyndonSuffixIndex_min (u ++ v) hw2
    · rw [hu1]
      omega
    · simp only [List.length_append]
      exact Nat.lt_add_of_pos_right (List.length_pos_of_ne_nil hv.1)
    · simp only [hu1]
      have hdrop : (u ++ v).drop 1 = v := by
        obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hu1
        simp
      rw [hdrop]
      exact (wittLyndon_iff_suffix v).mp hv
  have hk : k = u.length := by
    have hk0 := (wittLongestLyndonSuffixIndex_spec (u ++ v) hw2).1
    omega
  have hp : wittLongestLyndonPrefix (u ++ v) hw2 = u := by
    unfold wittLongestLyndonPrefix
    change (u ++ v).take k = u
    rw [hk]
    simp
  have hs : wittLongestLyndonSuffix (u ++ v) hw2 = v := by
    unfold wittLongestLyndonSuffix
    change (u ++ v).drop k = v
    rw [hk]
    simp
  rw [wittLyndonBracket]
  split_ifs with hlen
  · omega
  · simp only [hp, hs]

end MetaMathlibExt
