import Lemma.Complex.EqSquareSqrt
import Lemma.Int.SquareNeg.eq.Square
import Lemma.Real.OrEqS.of.Square
import Lemma.Set.In_Finset.is.OrEqS
open Real Complex Set Int


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.EqSquare.is.In_FinsetSqrt_NegSqrt |
| comm | Complex.In_FinsetSqrt_NegSqrt.is.EqSquare |
| mp | Complex.In_FinsetSqrt_NegSqrt.of.EqSquare |
| mpr | Complex.EqSquare.of.In_FinsetSqrt_NegSqrt |
-/
@[main, comm, mp, mpr]
private lemma main
  {x c : ℂ} :
-- imply
  x² = c ↔
    x ∈ ({√c, -√c} : Set ℂ) := by
-- proof
  constructor
  ·
    intro h
    apply In_Finset.of.OrEqS
    let t := √c
    have h_t : t² = c := EqSquareSqrt
    apply OrEqS.of.Square (h_t.symm ▸ h)
  ·
    intro hmem
    rw [In_Finset.is.OrEqS] at hmem
    obtain hx | hx := hmem
    ·
      rw [hx, EqSquareSqrt]
    ·
      rw [hx, SquareNeg.eq.Square, EqSquareSqrt]


-- created on 2024-07-01
-- updated on 2026-08-31
