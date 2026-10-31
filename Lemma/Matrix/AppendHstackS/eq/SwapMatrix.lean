import Initialize.Tactic.Attr.Basic
import Def.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Ring.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Lemma.Matrix.GetSwapMatrix.eq.Ite
open Matrix


@[path]
private lemma main
  [AddMonoidWithOne α]
-- given
  (i j : Fin n) :
-- imply
  (fromBlocks (swapMatrix (α := α) i j) 0 0 (1 : Matrix (Fin 1) (Fin 1) α)).reindex
    finSumFinEquiv finSumFinEquiv =
    swapMatrix (α := α) (Fin.castAdd 1 i) (Fin.castAdd 1 j) := by
-- proof
  ext a b
  simp only [reindex_apply, submatrix_apply]
  rcases hsa : finSumFinEquiv.symm a with ia | ia <;>
    rcases hsb : finSumFinEquiv.symm b with ib | ib
  ·
    have ha : a = Fin.castAdd 1 ia := by
      rw [← Equiv.apply_symm_apply finSumFinEquiv a, hsa, finSumFinEquiv_apply_left]
    have hb : b = Fin.castAdd 1 ib := by
      rw [← Equiv.apply_symm_apply finSumFinEquiv b, hsb, finSumFinEquiv_apply_left]
    rw [ha, hb, fromBlocks_apply₁₁, GetSwapMatrix.eq.Ite, GetSwapMatrix.eq.Ite]
    simp [Fin.ext_iff, Fin.val_castAdd]
  ·
    have ha : a = Fin.castAdd 1 ia := by
      rw [← Equiv.apply_symm_apply finSumFinEquiv a, hsa, finSumFinEquiv_apply_left]
    have hb : b = Fin.natAdd n ib := by
      rw [← Equiv.apply_symm_apply finSumFinEquiv b, hsb, finSumFinEquiv_apply_right]
    rw [ha, hb, fromBlocks_apply₁₂, GetSwapMatrix.eq.Ite]
    simp [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
    have : (ib : ℕ) < 1 := ib.isLt
    split_ifs <;> simp_all <;> omega
  ·
    have ha : a = Fin.natAdd n ia := by
      rw [← Equiv.apply_symm_apply finSumFinEquiv a, hsa, finSumFinEquiv_apply_right]
    have hb : b = Fin.castAdd 1 ib := by
      rw [← Equiv.apply_symm_apply finSumFinEquiv b, hsb, finSumFinEquiv_apply_left]
    rw [ha, hb, fromBlocks_apply₂₁, GetSwapMatrix.eq.Ite]
    simp [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
    have : (ia : ℕ) < 1 := ia.isLt
    split_ifs <;> simp_all <;> omega
  ·
    have ha : a = Fin.natAdd n ia := by
      rw [← Equiv.apply_symm_apply finSumFinEquiv a, hsa, finSumFinEquiv_apply_right]
    have hb : b = Fin.natAdd n ib := by
      rw [← Equiv.apply_symm_apply finSumFinEquiv b, hsb, finSumFinEquiv_apply_right]
    rw [ha, hb, fromBlocks_apply₂₂, GetSwapMatrix.eq.Ite]
    simp [one_apply, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
    have hia0 : ia = 0 := Fin.ext (by have := ia.isLt; omega)
    have hib0 : ib = 0 := Fin.ext (by have := ib.isLt; omega)
    subst hia0 hib0
    have hi := Nat.ne_of_lt i.isLt
    have hj := Nat.ne_of_lt j.isLt
    simp [hi.symm, hj.symm]


-- created on 2026-10-31
