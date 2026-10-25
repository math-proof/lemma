/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Def.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR.Part2
import Lemma.Finset.Enumerative.ULDMotzkinNumberOfRankR
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Def.Combinatorics.Enumerative.CubicLatticeColoredMotzkin.Part2


namespace MetaMathlibExt

/-- Forward map on a distinguished-coordinate step. -/
theorem cubeToMotzkinStep_of_eq (n : ℕ) (x : Fin (n + 1) × Bool)
    (h : x.1 = Fin.last n) : cubeToMotzkinStep n x = Sum.inl x.2 := by
  simp [cubeToMotzkinStep, h]

/-- Forward map on a flat step. -/
theorem cubeToMotzkinStep_of_ne (n : ℕ) (x : Fin (n + 1) × Bool)
    (h : ¬x.1 = Fin.last n) :
    cubeToMotzkinStep n x = Sum.inr (flatIndex n x h) := by
  simp [cubeToMotzkinStep, h]

/-- Encoding then decoding a flat index is the identity. -/
theorem div2_encode (a : ℕ) (b : Bool) :
    (a * 2 + (if b then 1 else 0)) / 2 = a ∧
    decide ((a * 2 + (if b then 1 else 0)) % 2 = 1) = b := by
  cases b
  · exact ⟨by simp, by simp⟩
  · constructor
    · simp
      omega
    · simp

/-- Decoding then encoding a flat color is the identity. -/
theorem mod2_decode (j : ℕ) :
    j / 2 * 2 + (if decide (j % 2 = 1) then 1 else 0) = j := by
  have hite : (if decide (j % 2 = 1) then (1 : ℕ) else 0) = j % 2 := by
    by_cases hc : j % 2 = 1
    · simp [hc]
    · have h0 : j % 2 = 0 := by omega
      simp [h0]
  rw [hite]
  omega

/-- Backward map is a left inverse of the forward map. -/
theorem step_left_inv (n : ℕ) (x : Fin (n + 1) × Bool) :
    motzkinToCubeStep n (cubeToMotzkinStep n x) = x := by
  by_cases h : x.1 = Fin.last n
  · rw [cubeToMotzkinStep_of_eq n x h]
    simp only [motzkinToCubeStep, Sum.elim_inl]
    exact Prod.ext h.symm rfl
  · rw [cubeToMotzkinStep_of_ne n x h]
    change ((⟨(flatIndex n x h).val / 2, by
      have hj := (flatIndex n x h).isLt
      omega⟩, decide ((flatIndex n x h).val % 2 = 1)) : Fin (n + 1) × Bool) = x
    obtain ⟨hd, hdec⟩ := div2_encode x.1.val x.2
    refine Prod.ext (Fin.ext_iff.mpr ?_) ?_
    · exact hd
    · exact hdec

/-- Forward map is a left inverse of the backward map. -/
theorem step_right_inv (n : ℕ) (y : Sum Bool (Fin (2 * n))) :
    cubeToMotzkinStep n (motzkinToCubeStep n y) = y := by
  cases y with
  | inl b =>
    simp only [motzkinToCubeStep, Sum.elim_inl]
    exact cubeToMotzkinStep_of_eq n _ rfl
  | inr j =>
    by_cases h : (motzkinToCubeStep n (Sum.inr j)).1 = Fin.last n
    · have hcon := congrArg Fin.val h
      rw [Fin.val_last] at hcon
      have hcon2 : j.val / 2 = n := hcon
      have hj2 : j.val / 2 < n := by
        have hj := j.isLt
        omega
      have hfalse : False := by omega
      exact False.elim hfalse
    · rw [cubeToMotzkinStep_of_ne n (motzkinToCubeStep n (Sum.inr j)) h]
      congr 1
      rw [Fin.ext_iff, flatIndex_val]
      have hval : (motzkinToCubeStep n (Sum.inr j)).1.val = j.val / 2 := rfl
      have hval2 : (motzkinToCubeStep n (Sum.inr j)).2 = decide (j.val % 2 = 1) :=
        rfl
      rw [hval, hval2]
      exact mod2_decode j

end MetaMathlibExt
