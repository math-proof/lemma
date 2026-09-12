import sympy.matrices.expressions.permutation
import Lemma.Nat.Delta.eq.Ite
import Lemma.Fin.Sum_Delta.eq.One
open Nat


@[main]
private lemma main
-- given
  (i j : Fin n) :
-- imply
  ∑ k ∈ Finset.Ico 1 n, KroneckerDelta (((i : ℕ) + k) % n) (j : ℕ) =
    if i = j then
      0
    else
      1 := by
-- proof
  have h : 0 < n := Fin.pos i
  let z : Fin n := ⟨0, h⟩
  have hcomm : ∀ (x : Fin n), (((i : ℕ) + (x : ℕ)) % n) = ((x + i : Fin n) : ℕ) := by
    intro x
    rw [Fin.val_add, add_comm (x : ℕ) (i : ℕ)]
  have hinj : Set.InjOn (fun x : Fin n => (x : ℕ)) (Finset.univ.erase z) :=
    fun _ _ _ _ hcon => Fin.ext hcon
  have hval : Finset.image (fun x : Fin n => (x : ℕ)) Finset.univ = Finset.range n := by
    ext k
    simp [Fin.exists_iff]
  have himg :
      Finset.image (fun x : Fin n => (x : ℕ)) (Finset.univ.erase z) = Finset.Ico 1 n := by
    rw [Finset.image_erase (fun _ _ hcon => Fin.ext hcon), hval]
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico, z]
    omega
  have hsum : ∑ k ∈ Finset.Ico 1 n, KroneckerDelta (((i : ℕ) + k) % n) (j : ℕ) =
      ∑ x ∈ Finset.univ.erase z,
        KroneckerDelta (((i : ℕ) + (x : ℕ)) % n) (j : ℕ) := by
    rw [← himg]
    exact Finset.sum_image hinj
  rw [hsum]
  have hcong :
      ∑ x ∈ Finset.univ.erase z, KroneckerDelta (((i : ℕ) + (x : ℕ)) % n) (j : ℕ) =
        ∑ x ∈ Finset.univ.erase z, KroneckerDelta ((x + i : Fin n) : ℕ) (j : ℕ) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [hcomm x]
  rw [hcong]
  have hall : ∑ x : Fin n, KroneckerDelta ((x + i : Fin n) : ℕ) (j : ℕ) =
      KroneckerDelta (i : ℕ) (j : ℕ) +
        ∑ x ∈ Finset.univ.erase z,
          KroneckerDelta ((x + i : Fin n) : ℕ) (j : ℕ) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ z)]
    have hzval : (z : ℕ) = 0 := by simp [z]
    have hz0 : (z + i : Fin n).val = (i : ℕ) := by
      rw [Fin.val_add, hzval, Nat.zero_add, Nat.mod_eq_of_lt i.is_lt]
    rw [Fin.ext hz0]
  have hsplit : KroneckerDelta (i : ℕ) (j : ℕ) +
      ∑ x ∈ Finset.univ.erase z, KroneckerDelta ((x + i : Fin n) : ℕ) (j : ℕ) = 1 :=
    hall.symm.trans (Fin.Sum_Delta.eq.One i j)
  have hkd : KroneckerDelta (i : ℕ) (j : ℕ) = if i = j then (1 : ℕ) else 0 := by
    simp [Nat.Delta.eq.Ite, Fin.ext_iff]
  have hsplit2 : (if i = j then (1 : ℕ) else 0) +
      ∑ x ∈ Finset.univ.erase z, KroneckerDelta ((x + i : Fin n) : ℕ) (j : ℕ) = 1 := by
    rw [← hkd]
    exact hsplit
  have hif : (if i = j then (1 : ℕ) else 0) + (if i = j then (0 : ℕ) else 1) = 1 := by
    split_ifs <;> rfl
  have heq : (if i = j then (1 : ℕ) else 0) +
      ∑ x ∈ Finset.univ.erase z, KroneckerDelta ((x + i : Fin n) : ℕ) (j : ℕ) =
      (if i = j then (1 : ℕ) else 0) + (if i = j then (0 : ℕ) else 1) := by
    rw [hsplit2, hif]
  exact Nat.add_left_cancel heq


-- created on 2026-09-12
