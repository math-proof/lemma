import sympy.core.power
import Lemma.Bool.Bool.eq.Zero.ou.Bool.eq.One
import Lemma.Nat.Mul.eq.Zero.of.OrEqS
import Lemma.Nat.Sub.eq.AddNeg
import Lemma.Int.Sub.eq.Zero.is.Eq
open Int Nat Bool


@[main, comm]
private lemma main
  [Decidable p] :
-- imply
  Bool.toNat p = (Bool.toNat p)² := by
-- proof
  have := Bool.eq.Zero.ou.Bool.eq.One (p := p)
  have := Mul.eq.Zero.of.OrEqS this
  ring_nf at this
  rw [AddNeg.eq.Sub] at this
  have := Eq.of.Sub.eq.Zero this
  norm_cast at this
  apply Eq.symm
  assumption


-- created on 2025-04-20
