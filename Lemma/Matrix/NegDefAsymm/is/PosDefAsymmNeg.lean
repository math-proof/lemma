import Lemma.Matrix.PosDefAsymm.is.PosDefAdd_T
import sympy.matrices.dense
open scoped Matrix


/--
| attributes | lemma |
| :---: | :---: |
| main | Matrix.NegDefAsymm.is.PosDefAsymmNeg |
| mp | Matrix.PosDefAsymmNeg.of.NegDefAsymm |
| mpr | Matrix.NegDefAsymm.of.PosDefAsymmNeg |
-/
@[main, mp, mpr]
private lemma main
  {α : Type*} [Fintype α]
-- given
  (A : Matrix α α ℝ) :
-- imply
  NegDefAsymm A ↔ PosDefAsymm (-A) := by
-- proof
  constructor
  case mp =>
    intro h
    exact h.nd
  case mpr =>
    intro h
    exact ⟨h⟩


-- created on 2026-09-19
