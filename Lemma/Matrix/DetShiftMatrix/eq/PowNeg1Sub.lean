import Initialize.Tactic.Attr.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Ring.Defs
import Def.LinearAlgebra.Matrix.Permutation
import Lemma.Matrix.GetShiftMatrix.eq.DeltaShiftRow
import Lemma.Nat.Delta.eq.Ite
open Equiv Matrix Nat


/--
Product of `k` adjacent swaps bubbling row `j₀` down to `j₀ + k`:
`swap(j₀+k-1, j₀+k) * … * swap(j₀, j₀+1)`.
-/
private def shiftPerm (n j₀ : ℕ) (hj : j₀ < n) (k : ℕ) (hk : j₀ + k < n) :
  Equiv.Perm (Fin n) :=
  match k with
  | 0 => 1
  | k + 1 =>
    Equiv.swap ⟨j₀ + k, by omega⟩ ⟨j₀ + k + 1, hk⟩ * shiftPerm n j₀ hj k (by omega)

private lemma shiftPerm_j0
  {n j₀ k : ℕ}
-- given
  (hj : j₀ < n)
  (hk : j₀ + k < n) :
-- imply
  shiftPerm n j₀ hj k hk ⟨j₀, hj⟩ = ⟨j₀ + k, hk⟩ := by
-- proof
  induction k with
  | zero =>
    rfl
  | succ k ih =>
    simp [shiftPerm, ih]
    rfl

private lemma shiftPerm_out
  {n j₀ : ℕ}
-- given
  (hj : j₀ < n) :
-- imply
  ∀ (k : ℕ) (hk : j₀ + k < n) (x : ℕ) (hx : x < n),
    (x < j₀ ∨ j₀ + k < x) →
      shiftPerm n j₀ hj k hk ⟨x, hx⟩ = ⟨x, hx⟩ := by
-- proof
  intro k
  induction k with
  | zero =>
    intro _ _ _ _
    rfl
  | succ k ih =>
    intro hk x hx h
    rw [shiftPerm, Equiv.Perm.mul_apply]
    have h' : x < j₀ ∨ j₀ + k < x := by omega
    rw [ih (by omega) x hx h']
    apply Equiv.swap_apply_of_ne_of_ne <;> simp [Fin.ext_iff] <;> omega

private lemma shiftPerm_mid
  {n j₀ t k : ℕ}
-- given
  (hj : j₀ < n)
  (ht1 : 1 ≤ t)
  (htk : t ≤ k)
  (hk : j₀ + k < n)
  (htm : j₀ + t < n)
  (htm1 : j₀ + t - 1 < n) :
-- imply
  shiftPerm n j₀ hj k hk ⟨j₀ + t, htm⟩ = ⟨j₀ + t - 1, htm1⟩ := by
-- proof
  induction k with
  | zero =>
    omega
  | succ k ih =>
    if ht : t ≤ k then
      rw [shiftPerm, Equiv.Perm.mul_apply, ih ht (by omega)]
      apply Equiv.swap_apply_of_ne_of_ne <;> simp [Fin.ext_iff] <;> omega
    else
      have htk' : t = k + 1 := by omega
      subst htk'
      rw [shiftPerm, Equiv.Perm.mul_apply]
      have hfix :
        shiftPerm n j₀ hj k (by omega) ⟨j₀ + (k + 1), by omega⟩ =
          ⟨j₀ + (k + 1), by omega⟩ :=
        shiftPerm_out hj k (by omega) (j₀ + (k + 1)) (by omega) (by omega)
      rw [hfix]
      have harg : (⟨j₀ + (k + 1), by omega⟩ : Fin n) = ⟨j₀ + k + 1, by omega⟩ :=
        rfl
      rw [harg, Equiv.swap_apply_right]
      apply Fin.ext
      rfl

/--
Determinant of the elementary row-shift matrix:
`det(shiftMatrix(n, i₀, j₀)) = (-1)^(i₀ - j₀)` when `j₀ < i₀`
(moving row `i₀` to position `j₀` takes `i₀ - j₀` adjacent swaps).
-/
@[path]
private lemma main
  [CommRing α]
  {i₀ j₀ : Fin n}
-- given
  (h : (j₀ : ℕ) < (i₀ : ℕ)) :
-- imply
  (shiftMatrix (α := α) i₀ j₀).det = (-1) ^ ((i₀ : ℕ) - (j₀ : ℕ)) := by
-- proof
  have hj : (j₀ : ℕ) < n := j₀.isLt
  let k := (i₀ : ℕ) - (j₀ : ℕ)
  have hk : (j₀ : ℕ) + k < n := by omega
  let σ : Equiv.Perm (Fin n) := shiftPerm n (j₀ : ℕ) hj k hk
  have hσ1 : σ j₀ = i₀ := by
    have h' := shiftPerm_j0 hj hk
    apply Fin.ext
    apply Eq.trans (congrArg Fin.val h')
    show (j₀ : ℕ) + k = (i₀ : ℕ)
    omega
  have hσ2 : ∀ (x : Fin n), (j₀ : ℕ) < (x : ℕ) → (x : ℕ) ≤ (i₀ : ℕ) →
    σ x = ⟨(x : ℕ) - 1, by omega⟩ := by
    intro x hx1 hx2
    have htk1 : 1 ≤ (x : ℕ) - (j₀ : ℕ) := by omega
    have htk : (x : ℕ) - (j₀ : ℕ) ≤ k := by omega
    have hxb : (j₀ : ℕ) + ((x : ℕ) - (j₀ : ℕ)) < n := by omega
    have heq0 : (j₀ : ℕ) + ((x : ℕ) - (j₀ : ℕ)) = (x : ℕ) := by omega
    have heq : x = ⟨(j₀ : ℕ) + ((x : ℕ) - (j₀ : ℕ)), hxb⟩ := by
      apply Fin.ext
      exact heq0.symm
    rw [heq]
    exact_mod_cast
      shiftPerm_mid hj htk1 htk hk (by omega) (by omega)
  have hσ3 : ∀ (x : Fin n), ((x : ℕ) < (j₀ : ℕ) ∨ (i₀ : ℕ) < (x : ℕ)) →
    σ x = x := by
    intro x hlt
    exact_mod_cast shiftPerm_out hj k hk (x : ℕ) x.isLt (by omega)
  have hσeq : ∀ i : Fin n, i.shiftRow i₀ j₀ = σ i := by
    intro i
    if hi : (i : ℕ) = (j₀ : ℕ) then
      have hi' : i = j₀ := Fin.ext hi
      rw [hi']
      refine Eq.trans ?_ hσ1.symm
      simp [Fin.shiftRow]
    else
      if hmid : (j₀ : ℕ) < (i : ℕ) ∧ (i : ℕ) ≤ (i₀ : ℕ) then
        refine Eq.trans ?_ (hσ2 i hmid.1 hmid.2).symm
        have hne : i ≠ j₀ := fun heq => hi (congrArg Fin.val heq)
        have hmem : i ∈ Set.Ioc j₀ i₀ :=
          ⟨Fin.lt_def.mpr hmid.1, Fin.le_def.mpr hmid.2⟩
        simp [Fin.shiftRow, hne, hmem]
      else
        refine Eq.trans ?_ (hσ3 i (by omega)).symm
        have hne : i ≠ j₀ := fun heq => hi (congrArg Fin.val heq)
        have hIoc : i ∉ Set.Ioc j₀ i₀ := by
          intro hin
          exact hmid ⟨Fin.lt_def.mp hin.1, Fin.le_def.mp hin.2⟩
        have hIco : i ∉ Set.Ico i₀ j₀ := by
          intro hin
          have : (i₀ : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (j₀ : ℕ) :=
            ⟨Fin.le_def.mp hin.1, Fin.lt_def.mp hin.2⟩
          omega
        simp [Fin.shiftRow, hne, hIoc, hIco]
  have hT : shiftMatrix (α := α) i₀ j₀ =
    (1 : Matrix (Fin n) (Fin n) α).submatrix σ id := by
    ext i j
    simp only [submatrix_apply, one_apply, id, GetShiftMatrix.eq.DeltaShiftRow, hσeq]
    simp [Delta.eq.Ite]
  have hsign : ∀ m : ℕ, ∀ (hm : (j₀ : ℕ) + m < n),
    Equiv.Perm.sign (shiftPerm n (j₀ : ℕ) hj m hm) = (-1 : Units ℤ) ^ m := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [shiftPerm, Equiv.Perm.sign_one]
    | succ m ih =>
      intro hmk1
      have hmk : (j₀ : ℕ) + m < n := by omega
      let a : Fin n := ⟨(j₀ : ℕ) + m, hmk⟩
      let b : Fin n := ⟨(j₀ : ℕ) + m + 1, hmk1⟩
      have hne : a ≠ b := by
        intro hcon
        have : ((j₀ : ℕ) + m : ℕ) = (j₀ : ℕ) + m + 1 := congrArg Fin.val hcon
        omega
      have hstep : shiftPerm n (j₀ : ℕ) hj (m + 1) hmk1 =
        Equiv.swap a b * shiftPerm n (j₀ : ℕ) hj m hmk :=
        rfl
      rw [hstep, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne, ih hmk]
      simp [pow_succ]
  rw [hT, Matrix.det_permute, Matrix.det_one, mul_one, hsign k hk]
  simp
  norm_cast


-- created on 2026-11-01
