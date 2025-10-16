import Lemma.Nat.EqMulS.of.Eq
import Lemma.Nat.Bool.eq.SquareBool
import Lemma.Algebra.Square.eq.Mul
import Lemma.Bool.Imp.is.Bool.eq.MulBoolS
open Algebra Bool Nat


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
-- given
  (h : Bool.toNat p = Bool.toNat q) :
-- imply
  p → q := by
-- proof
  have := EqMulS.of.Eq.left h (Bool.toNat p)
  rw [Mul.eq.Square] at this
  rw [SquareBool.eq.Bool] at this
  exact Imp.of.Bool.eq.MulBoolS this


-- created on 2025-04-20
