import Mathlib.Algebra.Ring.Defs
import Lemma.Matrix.GetShiftMatrix.eq.DeltaShiftRow
import Lemma.Nat.Delta.eq.Ite
open Matrix Nat


@[path]
private lemma main
  [AddMonoidWithOne α]
-- given
  (i₀ j₀ i j : Fin n) :
-- imply
  (shiftMatrix (α := α) i₀ j₀) i j =
    if (i₀ : ℕ) = (j₀ : ℕ) then
      (KroneckerDelta (i : ℕ) (j : ℕ) : α)
    else if (i₀ : ℕ) < (j₀ : ℕ) then
      if (i : ℕ) = (j₀ : ℕ) then
        (KroneckerDelta (i₀ : ℕ) (j : ℕ) : α)
      else if (i₀ : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (j₀ : ℕ) then
        (KroneckerDelta ((i : ℕ) + 1) (j : ℕ) : α)
      else
        (KroneckerDelta (i : ℕ) (j : ℕ) : α)
    else
      if (j : ℕ) = (i₀ : ℕ) then
        (KroneckerDelta (i : ℕ) (j₀ : ℕ) : α)
      else if (j₀ : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i₀ : ℕ) then
        (KroneckerDelta (i : ℕ) ((j : ℕ) + 1) : α)
      else
        (KroneckerDelta (i : ℕ) (j : ℕ) : α) := by
-- proof
  rw [GetShiftMatrix.eq.DeltaShiftRow i₀ j₀ i j]
  have hδ :
    KroneckerDelta (i.shiftRow i₀ j₀) j =
      KroneckerDelta (i.shiftRow i₀ j₀ : ℕ) (j : ℕ) := by
    simp [KroneckerDelta, Bool.toNat, Fin.ext_iff]
  have hrow :
    (i.shiftRow i₀ j₀ : ℕ) =
      if (i : ℕ) = (j₀ : ℕ) then
        ↑i₀
      else if (j₀ : ℕ) < (i : ℕ) ∧ (i : ℕ) ≤ (i₀ : ℕ) then
        i.val - 1
      else if (i₀ : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (j₀ : ℕ) then
        ↑i + 1
      else
        i := by
    simp only [Fin.shiftRow, Set.mem_Ioc, Set.mem_Ico, Fin.ext_iff]
    split_ifs <;> try rfl
    all_goals omega
  rw [hδ, Delta.eq.Ite, hrow]
  simp only [Delta.eq.Ite]
  split_ifs <;> try rfl
  all_goals omega


-- created on 2026-11-01
