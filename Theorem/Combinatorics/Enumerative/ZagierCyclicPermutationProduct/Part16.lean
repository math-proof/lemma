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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part16
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagCycleHit_spec {n : ℕ} (π : Equiv.Perm (Fin n))
    (a b : Fin n) (hab : π.SameCycle a b) :
    (π ^ zagCycleHit π a b hab) a = b :=
  Nat.find_spec hab.exists_nat_pow_eq

theorem zagCycleHit_pos {n : ℕ} (π : Equiv.Perm (Fin n))
    {a b : Fin n} (hab_ne : a ≠ b) (hab : π.SameCycle a b) :
    0 < zagCycleHit π a b hab := by
  by_contra h
  have hz : zagCycleHit π a b hab = 0 := Nat.eq_zero_of_not_pos h
  have heq : a = b := by
    simpa only [hz, pow_zero, Equiv.Perm.one_apply] using
      zagCycleHit_spec π a b hab
  exact hab_ne heq

theorem zagCycleHit_minimal {n : ℕ} (π : Equiv.Perm (Fin n))
    (a b : Fin n) (hab : π.SameCycle a b) {r : ℕ}
    (hr : (π ^ r) a = b) : zagCycleHit π a b hab ≤ r :=
  Nat.find_min' hab.exists_nat_pow_eq hr

theorem zagCycleHit_no_return {n : ℕ} (π : Equiv.Perm (Fin n))
    {a b : Fin n} (hab : π.SameCycle a b)
    {r : ℕ} (hr0 : 0 < r) (hrH : r < zagCycleHit π a b hab) :
    (π ^ r) a ≠ a := by
  let H := zagCycleHit π a b hab
  intro hreturn
  have hearly : (π ^ (H - r)) a = b := by
    calc
      (π ^ (H - r)) a = (π ^ (H - r)) ((π ^ r) a) := by rw [hreturn]
      _ = (π ^ ((H - r) + r)) a := by
        rw [pow_add, Equiv.Perm.mul_apply]
      _ = (π ^ H) a := by congr 2; omega
      _ = b := by simpa [H] using zagCycleHit_spec π a b hab
  have hmin : H ≤ H - r := zagCycleHit_minimal π a b hab hearly
  omega

theorem zagMulSwap_sameCycle_right_arc {n : ℕ}
    (π : Equiv.Perm (Fin n)) {a c x : Fin n}
    (hac_ne : a ≠ c) (hac : π.SameCycle a c)
    (hx : (π * Equiv.swap a c).SameCycle c x) :
    ∃ r : ℕ, 0 < r ∧ r ≤ zagCycleHit π a c hac ∧
      (π ^ r) a = x := by
  let H := zagCycleHit π a c hac
  let g := π * Equiv.swap a c
  have hHpos : 0 < H := zagCycleHit_pos π hac_ne hac
  obtain ⟨m, hm⟩ := hx.exists_nat_pow_eq
  have hstate : ∀ q : ℕ, ∃ r : ℕ, 0 < r ∧ r ≤ H ∧
      (g ^ q) c = (π ^ r) a := by
    intro q
    induction q with
    | zero =>
        exact ⟨H, hHpos, le_rfl, by
          simpa [H] using (zagCycleHit_spec π a c hac).symm⟩
    | succ q ih =>
        obtain ⟨r, hr0, hrH, hqr⟩ := ih
        by_cases hre : r = H
        · refine ⟨1, by omega, hHpos, ?_⟩
          calc
            (g ^ (q + 1)) c = g ((g ^ q) c) := by
              simpa only [Equiv.Perm.mul_apply] using
                congrArg (fun p : Equiv.Perm (Fin n) => p c) (pow_succ' g q)
            _ = g ((π ^ r) a) := by rw [hqr]
            _ = g c := by
              rw [hre]
              simpa [H] using zagCycleHit_spec π a c hac
            _ = π a := by simp [g, Equiv.Perm.mul_apply]
            _ = (π ^ 1) a := by simp
        · have hrlt : r < H := lt_of_le_of_ne hrH hre
          have hra : (π ^ r) a ≠ a :=
            zagCycleHit_no_return π hac hr0 hrlt
          have hrc : (π ^ r) a ≠ c := fun hrc =>
            (not_lt_of_ge (zagCycleHit_minimal π a c hac hrc)) hrlt
          refine ⟨r + 1, by omega, by omega, ?_⟩
          calc
            (g ^ (q + 1)) c = g ((g ^ q) c) := by
              simpa only [Equiv.Perm.mul_apply] using
                congrArg (fun p : Equiv.Perm (Fin n) => p c) (pow_succ' g q)
            _ = g ((π ^ r) a) := by rw [hqr]
            _ = π ((π ^ r) a) := by
              simp [g, Equiv.Perm.mul_apply,
                Equiv.swap_apply_of_ne_of_ne hra hrc]
            _ = (π ^ (r + 1)) a := by
              simpa only [Equiv.Perm.mul_apply] using
                (congrArg (fun p : Equiv.Perm (Fin n) => p a)
                  (pow_succ' π r)).symm
  obtain ⟨r, hr0, hrH, hr⟩ := hstate m
  exact ⟨r, hr0, hrH, hr.symm.trans hm⟩

theorem zagFirstSwap_pow_between {n : ℕ}
    (π : Equiv.Perm (Fin n)) {a b c : Fin n}
    (hab : π.SameCycle a b) (hac : π.SameCycle a c)
    (hbefore : zagCycleHit π a c hac < zagCycleHit π a b hab)
    {r : ℕ} (hr0 : 0 < r)
    (hrle : r ≤ zagCycleHit π a b hab - zagCycleHit π a c hac) :
    ((π * Equiv.swap a c) ^ r) a =
      (π ^ (zagCycleHit π a c hac + r)) a := by
  let T := zagCycleHit π a c hac
  let H := zagCycleHit π a b hab
  let h := π * Equiv.swap a c
  induction r using Nat.case_strong_induction_on with
  | hz => omega
  | hi r ih =>
      by_cases hrz : r = 0
      · subst r
        calc
          (h ^ (0 + 1)) a = h a := by simp
          _ = π c := by simp [h, Equiv.Perm.mul_apply]
          _ = π ((π ^ T) a) := by
            rw [zagCycleHit_spec π a c hac]
          _ = (π ^ (T + (0 + 1))) a := by
            simpa only [Nat.zero_add, Equiv.Perm.mul_apply] using
              (congrArg (fun p : Equiv.Perm (Fin n) => p a)
                (pow_succ' π T)).symm
      · have hr0' : 0 < r := Nat.pos_of_ne_zero hrz
        have hrle' : r ≤ H - T := by omega
        have ihr := ih r le_rfl hr0' hrle'
        have hur : T + r < H := by omega
        have hne_a : (π ^ (T + r)) a ≠ a :=
          zagCycleHit_no_return π hab (by omega) hur
        have hne_c : (π ^ (T + r)) a ≠ c := by
          intro heq
          have hreturn : (π ^ r) a = a := by
            apply (π ^ T).injective
            calc
              (π ^ T) ((π ^ r) a) = (π ^ (T + r)) a := by
                rw [pow_add, Equiv.Perm.mul_apply]
              _ = c := heq
              _ = (π ^ T) a := (zagCycleHit_spec π a c hac).symm
          exact zagCycleHit_no_return π hab hr0' (by omega) hreturn
        calc
          (h ^ (r + 1)) a = h ((h ^ r) a) := by
            simpa only [Equiv.Perm.mul_apply] using
              congrArg (fun p : Equiv.Perm (Fin n) => p a) (pow_succ' h r)
          _ = h ((π ^ (T + r)) a) := by rw [ihr]
          _ = π ((π ^ (T + r)) a) := by
            simp [h, Equiv.Perm.mul_apply,
              Equiv.swap_apply_of_ne_of_ne hne_a hne_c]
          _ = (π ^ (T + (r + 1))) a := by
            rw [show T + (r + 1) = (T + r) + 1 by omega]
            simpa only [Equiv.Perm.mul_apply] using
              (congrArg (fun p : Equiv.Perm (Fin n) => p a)
                (pow_succ' π (T + r))).symm

end MetaMathlibExt
