import sympy.core.logic
import Lemma.Bool.Cond.is.Bool.eq.One
import Lemma.Bool.Imp.of.Imp.Imp
import Lemma.Bool.Imp.is.Or_Not
import Lemma.Bool.Bool.eq.Zero.of.Bool.ne.One
import Lemma.Algebra.Mul.eq.Zero.of.OrEqS
import Lemma.Algebra.MulSub.eq.SubMulS
import Lemma.Nat.Mul
import Lemma.Nat.EqCoeS.is.Eq
import Lemma.Algebra.Sub.eq.Zero.is.Eq
import Lemma.Nat.CoeMul.eq.MulCoeS
import Lemma.Algebra.Sub_Mul.eq.Mul_Sub1
import Lemma.Algebra.Mul.eq.Zero.is.OrEqS_0
import Lemma.Algebra.Ne_1.of.Eq_0
import Lemma.Bool.Ne.is.NotEq
import Lemma.Bool.Imp.is.OrNot
open Algebra Bool Nat


@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
  [Decidable q] :
-- imply
  p → q ↔ Bool.toNat p = Bool.toNat p * Bool.toNat q := by
-- proof
  constructor <;>
    intro h
  .
    have h_P := Cond.of.Bool.eq.One (p := p)
    have h_Q := Bool.eq.One.of.Cond (p := q)
    have := Imp.of.Imp.Imp h h_Q
    have := Imp.of.Imp.Imp h_P this
    have := Or_Not.of.Imp this
    mp [Bool.eq.Zero.of.Bool.ne.One (p := p)] at this
    have := Mul.eq.Zero.of.OrEqS.nat this
    rw [MulSub.eq.SubMulS] at this
    simp at this
    have := Eq.of.Sub.eq.Zero this
    have := Eq.of.EqCoeS this
    rw [Mul.comm]
    apply Eq.symm
    assumption
  .
    have := EqCoeS.of.Eq (R := ℤ) h
    rw [CoeMul.eq.MulCoeS] at this
    have := Sub.eq.Zero.of.Eq this
    rw [Sub_Mul.eq.Mul_Sub1] at this
    have := OrEqS_0.of.Mul.eq.Zero this
    mp [Eq.of.Sub.eq.Zero (a := (1 : ℤ)) (b := (Bool.toNat q : ℤ))] at this
    -- mp [Eq.of.Sub.eq.Zero] at this
    mp [Ne_1.of.Eq_0 (a := (Bool.toNat p : ℤ))] at this
    rw [Ne.is.NotEq] at this
    have := Imp.of.OrNot this
    norm_cast at this
    rw [Bool.eq.One.is.Cond] at this
    rw [Eq.comm] at this
    rwa [Bool.eq.One.is.Cond] at this


-- created on 2025-04-20
