/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part4


namespace MetaMathlibExt

lemma pgf_joinFirst_top {n m : ℕ} (d : pgfFirstData n m) :
    pgf_joinFirst d d.1 = Fin.last m := by
  simp [pgf_joinFirst]

lemma pgf_joinFirst_before {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
    (v : Fin (n - 1 - i.val) → Fin (m + 1)) (j : Fin i.val) :
    pgf_joinFirst ⟨i, u, v⟩ ⟨j.val, lt_trans j.isLt i.isLt⟩ = (u j).castSucc := by
  simp [pgf_joinFirst, j.isLt]

lemma pgf_joinFirst_after {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
    (v : Fin (n - 1 - i.val) → Fin (m + 1)) (j : Fin (n - 1 - i.val)) :
    pgf_joinFirst ⟨i, u, v⟩ ⟨i.val + 1 + j.val, by omega⟩ = v j := by
  unfold pgf_joinFirst
  dsimp
  have hnlt : ¬i.val + 1 + j.val < i.val := by omega
  have hneq : i.val + 1 + j.val ≠ i.val := by omega
  rw [dite_eq_right hnlt, dite_eq_right hneq]
  congr 1
  apply Fin.ext
  change (i.val + 1 + j.val - i.val - 1) = j.val
  omega

lemma pgf_joinFirst_top_le {n m : ℕ} (d : pgfFirstData n m) (j : Fin n)
    (h : pgf_joinFirst d j = Fin.last m) : d.1.val ≤ j.val := by
  by_contra hnle
  have hlt : j.val < d.1.val := by omega
  unfold pgf_joinFirst at h
  rw [dite_eq_left hlt] at h
  exact Fin.castSucc_ne_last _ h

lemma pgf_joinFirst_injective (n m : ℕ) :
    Function.Injective (@pgf_joinFirst n m) := by
  rintro ⟨i, u, v⟩ ⟨i', u', v'⟩ h
  have hii' : i.val ≤ i'.val := by
    apply pgf_joinFirst_top_le ⟨i, u, v⟩ i'
    have hi' := congrFun h i'
    rw [pgf_joinFirst_top] at hi'
    exact hi'
  have hi'i : i'.val ≤ i.val := by
    apply pgf_joinFirst_top_le ⟨i', u', v'⟩ i
    have hi := congrFun h i
    rw [pgf_joinFirst_top] at hi
    exact hi.symm
  have heq : i = i' := Fin.ext (by omega)
  subst i'
  have hu : u = u' := by
    funext j
    apply Fin.castSucc_injective
    have hj := congrFun h ⟨j.val, lt_trans j.isLt i.isLt⟩
    simpa only [pgf_joinFirst_before] using hj
  have hv : v = v' := by
    funext j
    have hj := congrFun h ⟨i.val + 1 + j.val, by omega⟩
    simpa only [pgf_joinFirst_after] using hj
  subst u'
  subst v'
  rfl

end MetaMathlibExt
