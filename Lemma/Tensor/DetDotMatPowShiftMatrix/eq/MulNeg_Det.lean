import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.RowCol
import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.Det.eq.DetToMatrix
import Lemma.Tensor.GetMatPowShiftMatrix.eq.Mod
import Lemma.Tensor.GetSum.eq.Sum_Get.of.GtLength_0
import Lemma.Tensor.Mul
import Lemma.Tensor.ToMatrixDot.eq.MulToMatrixS
import sympy.matrices.expressions.matpow
open Matrix Nat Tensor


/--
Translation `x ↦ x + i` on `Fin n`.
-/
private def finAddRight (n : ℕ) (h : 0 < n) (i : Fin n) : Equiv (Fin n) (Fin n) where
  toFun x := x + i
  invFun y := ⟨((y : ℕ) + n - (i : ℕ)) % n, Nat.mod_lt _ h⟩
  left_inv x := by
    apply Fin.ext
    show (((x : ℕ) + (i : ℕ)) % n + n - (i : ℕ)) % n = (x : ℕ)
    have hx : (x : ℕ) < n := x.isLt
    have hi : (i : ℕ) < n := i.isLt
    have hmod1 : ∀ (a : ℕ), a < n → (a + n) % n = a := by
      intro a ha
      have key : (a + n) % n = a % n := by
        have e : a + n = a + n * 1 := by simp
        rw [e, Nat.add_mul_mod_self_left]
      exact key.trans (Nat.mod_eq_of_lt ha)
    by_cases h : (x : ℕ) + (i : ℕ) < n
    · rw [Nat.mod_eq_of_lt h]
      have h2 : (x : ℕ) + (i : ℕ) + n - (i : ℕ) = x + n := by omega
      rw [h2]
      exact hmod1 x hx
    · have h' : n ≤ (x : ℕ) + (i : ℕ) := by omega
      have hlt : (x : ℕ) + (i : ℕ) - n < n := by omega
      have hsub : (x : ℕ) + (i : ℕ) = n + ((x : ℕ) + (i : ℕ) - n) :=
        (Nat.add_sub_of_le h').symm
      have hm : ((x : ℕ) + (i : ℕ)) % n = (x : ℕ) + (i : ℕ) - n := by
        conv_lhs => rw [hsub, Nat.add_comm]
        exact hmod1 ((x : ℕ) + (i : ℕ) - n) hlt
      rw [hm]
      have h3 : (x : ℕ) + (i : ℕ) - n + n - (i : ℕ) = x := by omega
      rw [h3]
      exact Nat.mod_eq_of_lt hx
  right_inv y := by
    apply Fin.ext
    show (((y : ℕ) + n - (i : ℕ)) % n + (i : ℕ)) % n = (y : ℕ)
    have hy : (y : ℕ) < n := y.isLt
    have hi : (i : ℕ) < n := i.isLt
    have hmod1 : ∀ (a : ℕ), a < n → (a + n) % n = a := by
      intro a ha
      have key : (a + n) % n = a % n := by
        have e : a + n = a + n * 1 := by simp
        rw [e, Nat.add_mul_mod_self_left]
      exact key.trans (Nat.mod_eq_of_lt ha)
    rw [Nat.mod_add_mod]
    have h : (y : ℕ) + n - (i : ℕ) + (i : ℕ) = y + n := by omega
    rw [h]
    exact hmod1 y hy


/--
Summing the cyclic deltas over `k ∈ [1, n)` leaves exactly the off-diagonal entries:
`∑_{k=1}^{n-1} KroneckerDelta ((i + k) % n) j = if i = j then 0 else 1`.
-/
private lemma sum_delta
  (n : ℕ) (h : 0 < n) (i j : Fin n) :
  ∑ k ∈ Finset.Ico 1 n, KroneckerDelta (((i : ℕ) + k) % n) (j : ℕ) =
    if i = j then 0 else 1 := by
  let z : Fin n := ⟨0, h⟩
  have hcomm : ∀ (x : Fin n), (((i : ℕ) + (x : ℕ)) % n) = ((x + i : Fin n) : ℕ) := by
    intro x
    rw [Fin.val_add, add_comm (x : ℕ) (i : ℕ)]
  have hbij : ∑ x : Fin n, KroneckerDelta ((x + i : Fin n) : ℕ) (j : ℕ) = 1 := by
    rw [Fintype.sum_equiv (finAddRight n h i)
        (fun x => KroneckerDelta ((x + i : Fin n) : ℕ) (j : ℕ))
        (fun y => KroneckerDelta (y : ℕ) (j : ℕ))
        (fun _ => rfl)]
    rw [Finset.sum_eq_single j]
    · simp [Delta.eq.Ite]
    · intro y _ hy
      simp only [Delta.eq.Ite]
      exact if_neg (fun hcon => hy (Fin.ext hcon))
    · intro hx
      exact False.elim (hx (Finset.mem_univ j))
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
  have hcong : ∑ x ∈ Finset.univ.erase z,
        KroneckerDelta (((i : ℕ) + (x : ℕ)) % n) (j : ℕ) =
      ∑ x ∈ Finset.univ.erase z,
        KroneckerDelta ((x + i : Fin n) : ℕ) (j : ℕ) := by
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
    hall.symm.trans hbij
  by_cases hij : i = j
  · subst hij
    simp only [Delta.eq.Ite, if_true] at hsplit ⊢
    omega
  · have hne : (i : ℕ) ≠ (j : ℕ) := by
      intro hcon
      exact hij (Fin.ext hcon)
    simp only [Delta.eq.Ite, if_neg hne, if_neg hij] at hsplit ⊢
    omega


/--
`det (J - 1) = (-1)^(n-1) * (n - 1)` where `J` is the all-ones matrix,
by the matrix determinant lemma with `J` a column times a row of ones.
-/
private lemma det_sub_one
  [CommRing β] (n : ℕ) (h : 0 < n) :
  Matrix.det (fun i j : Fin n => if i = j then (0 : β) else 1) =
    (-1 : β) ^ (n - 1) * (n - 1 : ℕ) := by
  let u : Fin n → β := fun _ => 1
  let J := Matrix.replicateCol (Fin 1) u * Matrix.replicateRow (Fin 1) u
  have hJ : ∀ (i j : Fin n), J i j = (1 : β) := by
    intro i j
    simp only [J, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]
    rw [Finset.sum_eq_single (0 : Fin 1)]
    · simp only [u]
      exact one_mul (1 : β)
    · intro x _ hx
      exact False.elim (hx (Fin.fin_one_eq_zero x))
    · intro hx
      exact False.elim (hx (Finset.mem_univ (0 : Fin 1)))
  have hM : (fun i j : Fin n => if i = j then (0 : β) else 1) =
      J - (1 : Matrix (Fin n) (Fin n) β) := by
    ext i j
    rw [Matrix.sub_apply, hJ i j, Matrix.one_apply]
    split_ifs <;> simp
  rw [hM]
  have hneg : J - (1 : Matrix (Fin n) (Fin n) β) =
      - ((1 : Matrix (Fin n) (Fin n) β) - J) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.one_apply, hJ i j]
    ring
  rw [hneg, Matrix.det_neg,
    Matrix.det_one_sub_mul_comm
      (A := Matrix.replicateCol (Fin 1) u)
      (B := Matrix.replicateRow (Fin 1) u)]
  have h1 : Matrix.det ((1 : Matrix (Fin 1) (Fin 1) β) -
      Matrix.replicateRow (Fin 1) u * Matrix.replicateCol (Fin 1) u) =
      1 - (n : β) := by
    simp [Matrix.replicateRow_mul_replicateCol_apply,
      dotProduct, u, Finset.sum_const]
  rw [h1]
  have hn : n = (n - 1) + 1 := by omega
  rw [hn]
  simp [pow_succ]


@[main]
private lemma main
  [CommRing α] [CharZero α]
  (n : ℕ)
  (h : 0 < n)
  (A : Tensor α [n, n]) :
-- imply
  (∑ k ∈ Finset.Ico 1 n,
      ((ShiftMatrix (α := α) n 0 (n - 1) ^ (k : ℤ)) @ A : Tensor α [n, n])).det =
    (-1 : Tensor α []) ^ (n - 1) * (↑(n - 1) : Tensor α []) *
      id (α := Tensor α []) A.det := by
-- proof
  let S := ShiftMatrix (α := α) n 0 (n - 1)
  let P : Tensor α [n, n] := ∑ k ∈ Finset.Ico 1 n, S ^ (k : ℤ)
  let L : Tensor α [n, n] :=
    ∑ k ∈ Finset.Ico 1 n, ((S ^ (k : ℤ)) @ A : Tensor α [n, n])
  have hsum_toMatrix : ∀ (X : ℕ → Tensor α [n, n]),
      (∑ k ∈ Finset.Ico 1 n, X k).toMatrix =
        ∑ k ∈ Finset.Ico 1 n, (X k).toMatrix := by
    intro X
    apply Matrix.ext
    intro i j
    simp only [Tensor.toMatrix, GetElem.getElem]
    erw [Finset.sum_apply, Finset.sum_apply]
    simp only [Tensor.toMatrix, GetElem.getElem]
    erw [Tensor.GetSum.eq.Sum_Get.of.GtLength_0 (s := [n, n]) (by simp) X i,
      Tensor.GetSum.eq.Sum_Get.of.GtLength_0 (s := [n]) (by simp)
        (fun k => (X k).get i) j]
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun x : Fin n => ((X k).get x).get j) (Fin.ext rfl)
  let f (k : ℕ) : Tensor α [n, n] := S ^ (k : ℤ)
  let g (k : ℕ) : Tensor α [n, n] := (f k) @ A
  have hL : L.toMatrix = P.toMatrix * A.toMatrix := by
    show (∑ k ∈ Finset.Ico 1 n, g k).toMatrix = _
    rw [hsum_toMatrix g, hsum_toMatrix f]
    have hm : ∑ k ∈ Finset.Ico 1 n, (g k).toMatrix =
        ∑ k ∈ Finset.Ico 1 n, (f k).toMatrix * A.toMatrix := by
      apply Finset.sum_congr rfl
      intro k _
      exact Tensor.ToMatrixDot.eq.MulToMatrixS (f k) A
    rw [hm, Matrix.sum_mul]
  let M : Matrix (Fin n) (Fin n) (Tensor α []) :=
    fun i j => ↑(if i = j then (0 : Nat) else 1)
  have hcast : ∀ (i j : Fin n),
      M i j = if i = j then (0 : Tensor α []) else 1 := by
    intro i j
    simp only [M]
    split_ifs
    · exact Nat.cast_zero
    · exact Nat.cast_one
  have hP : P.toMatrix = M := by
    ext i j
    rw [hsum_toMatrix f]
    erw [Finset.sum_apply, Finset.sum_apply]
    have hdelta : ∀ c ∈ Finset.Ico 1 n, (f c).toMatrix i j =
        (↑(KroneckerDelta (((i : ℕ) + c) % n) (j : ℕ)) : Tensor α []) := by
      intro c _
      simp only [f, Tensor.toMatrix]
      exact Tensor.GetMatPowShiftMatrix.eq.Mod n h c i j
    rw [Finset.sum_congr rfl hdelta]
    erw [← Nat.cast_sum]
    rw [sum_delta n h i j]
    have hc : (↑(if i = j then (0 : Nat) else 1) : Tensor α []) =
        (if i = j then (0 : Tensor α []) else 1) := by
      split_ifs
      · exact Nat.cast_zero
      · exact Nat.cast_one
    exact hc.trans (hcast i j).symm
  have hM' : M = (fun i j : Fin n => if i = j then (0 : Tensor α []) else 1) := by
    ext i j
    exact hcast i j
  have hdetM : M.det =
      (-1 : Tensor α []) ^ (n - 1) * (↑(n - 1) : Tensor α []) := by
    rw [hM']
    have hd := det_sub_one (β := Tensor α []) n h
    rw [Tensor.Mul ((-1 : Tensor α []) ^ (n - 1)) (↑(n - 1) : Tensor α [])]
    exact hd
  have hstep1 : L.toMatrix.det = (P.toMatrix * A.toMatrix).det := by rw [hL]
  show L.det = _
  rw [Det.eq.DetToMatrix L, hstep1, Matrix.det_mul, hP, hdetM]
  rw [← Det.eq.DetToMatrix A]
  exact (Tensor.Mul _ (id (α := Tensor α []) A.det)).symm


-- created on 2020-10-03
