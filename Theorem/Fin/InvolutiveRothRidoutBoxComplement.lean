module

public import Mathlib
public import Theorem.Fin.GetRothRidoutBoxComplement.eq.Sub.of.RothBox

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothRidoutBoxComplement_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.InvolutiveRothRidoutBoxComplement
  {m : ℕ}
-- given
  (r : Fin m → ℕ) :
-- imply
  Function.Involutive (rothRidoutBoxComplement r) := by
-- proof
  intro j
  funext h
  apply Fin.ext
  rw [GetRothRidoutBoxComplement.eq.Sub.of.RothBox,
    GetRothRidoutBoxComplement.eq.Sub.of.RothBox]
  have hj : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
  omega


-- created on 2026-10-21
