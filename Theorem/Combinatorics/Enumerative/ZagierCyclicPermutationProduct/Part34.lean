/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part31
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagSliceOrder_basePoint {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (x : Fin n)
    (hx : zagNontrivialAntiExceedance e π x) :
    zagSliceOrder e π x hx (zagBasePoint x) = e (zagBasePoint x) := by
  simpa only [zagBasePoint] using zagSliceOrder_apply_zero e π x hx

theorem zagFullSlice_diagonal {n : ℕ} (p : ZagPointedPlane n) :
    zagDiagonal (zagFullSlice p).out.order (zagFullSlice p).out.vertical =
      zagDiagonal p.order p.vertical := by
  fun_induction zagFullSlice p with
  | case1 p e' π' hres m p' next hmfirst hmmiddle hmiddle_root ih _ =>
      exact ih.trans (zagSlice_diagonal p.order p.vertical p.point
        p.point_property)
  | case2 p e' π' hterm m =>
      exact zagSlice_diagonal p.order p.vertical p.point p.point_property

theorem zagFullSlice_basePoint {n : ℕ} (p : ZagPointedPlane n) :
    (zagFullSlice p).out.order (zagBasePoint p.point) =
      p.order (zagBasePoint p.point) := by
  fun_induction zagFullSlice p with
  | case1 p e' π' hres m p' next hmfirst hmmiddle hmiddle_root ih _ =>
      exact ih.trans (zagSliceOrder_basePoint p.order p.vertical p.point
        p.point_property)
  | case2 p e' π' hterm m =>
      exact zagSliceOrder_basePoint p.order p.vertical p.point p.point_property

theorem zagFullSlice_cycleCount {n : ℕ} (p : ZagPointedPlane n) :
    cycleQuotientCount (zagFullSlice p).out.vertical =
      cycleQuotientCount p.vertical +
        2 * ((zagFullSlice p).out.marks.depth + 1) := by
  fun_induction zagFullSlice p with
  | case1 p e' π' hres m p' next hmfirst hmmiddle hmiddle_root ih _ =>
      change cycleQuotientCount next.out.vertical =
        cycleQuotientCount p.vertical +
          2 * (next.out.marks.depth + 1 + 1)
      calc
        cycleQuotientCount next.out.vertical =
            cycleQuotientCount p'.vertical +
              2 * (next.out.marks.depth + 1) := ih
        _ = (cycleQuotientCount p.vertical + 2) +
              2 * (next.out.marks.depth + 1) := by
            rw [zagSliceVertical_count]
        _ = cycleQuotientCount p.vertical +
              2 * (next.out.marks.depth + 1 + 1) := by omega
  | case2 p e' π' hterm m =>
      change cycleQuotientCount
          (zagSliceVertical p.order p.vertical p.point p.point_property) =
        cycleQuotientCount p.vertical + 2 * (0 + 1)
      rw [zagSliceVertical_count]

theorem zagFinRotate_cycleCount (n : ℕ) (hn : 0 < n) :
    cycleQuotientCount (finRotate n) = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  cases m with
  | zero =>
      rw [Subsingleton.elim (finRotate 1) 1]
      simp [cycleQuotientCount_eq]
  | succ m =>
      rw [cycleQuotientCount_eq, Equiv.Perm.card_fixedPoints,
        cycleType_finRotate]
      simp

theorem zagHorizontal_cycleCount {n : ℕ}
    (e : Equiv.Perm (Fin n)) (hn : 0 < n) :
    cycleQuotientCount (zagHorizontal e) = 1 := by
  rw [cycleQuotientCount_eq, Equiv.Perm.card_fixedPoints,
    zagHorizontal, Equiv.Perm.cycleType_conj]
  simpa only [cycleQuotientCount_eq, Equiv.Perm.card_fixedPoints] using
    zagFinRotate_cycleCount n hn

theorem zagCycleType_eq_finRotate_of_cycleCount_one {n : ℕ}
    (hn : 0 < n) (s : Equiv.Perm (Fin n))
    (hs : cycleQuotientCount s = 1) :
    s.cycleType = (finRotate n).cycleType := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  cases m with
  | zero =>
      congr 1
      exact Subsingleton.elim s (finRotate 1)
  | succ m =>
      have hs' : Multiset.card s.cycleType +
          ((m + 2) - s.cycleType.sum) = 1 := by
        simpa only [cycleQuotientCount_eq,
          Equiv.Perm.card_fixedPoints, Fintype.card_fin] using hs
      have hcard_le : Multiset.card s.cycleType ≤ 1 := by omega
      have hcard_ne : Multiset.card s.cycleType ≠ 0 := by
        intro hzero
        have htype : s.cycleType = 0 := Multiset.card_eq_zero.mp hzero
        rw [htype] at hs'
        simp only [Multiset.card_zero, Multiset.sum_zero, Nat.zero_add] at hs'
        omega
      have hcard : Multiset.card s.cycleType = 1 := by omega
      obtain ⟨r, hr⟩ := Multiset.card_eq_one.mp hcard
      have hrsum : r ≤ m + 2 := by
        simpa only [hr, Multiset.sum_singleton, Fintype.card_fin] using
          s.sum_cycleType_le
      have hrn : r = m + 2 := by
        rw [hr] at hs'
        simp only [Multiset.card_singleton, Multiset.sum_singleton] at hs'
        omega
      rw [hr, hrn, cycleType_finRotate]

theorem zagFinRotate_pow_base {n : ℕ} (i : Fin n) :
    ((finRotate n) ^ i.val) (zagBasePoint i) = i := by
  change ((finRotate n)^[i.val]) (zagBasePoint i) = i
  rw [← finCycle_eq_finRotate_iterate]
  change zagBasePoint i + i = i
  apply Fin.ext
  simp [Fin.add_def, zagBasePoint, Nat.mod_eq_of_lt i.isLt]

theorem zagConj_pow {n m : ℕ}
    (e r : Equiv.Perm (Fin n)) :
    (e * r * e⁻¹) ^ m = e * r ^ m * e⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', pow_succ', ih]
      group

theorem zagHorizontal_pow_base {n : ℕ}
    (e : Equiv.Perm (Fin n)) (i : Fin n) :
    (zagHorizontal e ^ i.val) (e (zagBasePoint i)) = e i := by
  rw [zagHorizontal, zagConj_pow]
  simp only [Equiv.Perm.mul_apply]
  change e (((finRotate n) ^ i.val) (e.symm (e (zagBasePoint i)))) = e i
  rw [e.symm_apply_apply, zagFinRotate_pow_base]

end MetaMathlibExt
