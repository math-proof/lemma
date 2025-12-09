import Lemma.Int.Mul.gt.Zero.is.AndGtS_0.ou.AndLtS_0
import Lemma.Rat.LtInvS.is.Lt.of.Gt0.Gt0
import Lemma.Rat.LtInvS.is.Lt.of.Lt0.Lt0
open Rat Int


@[main, comm 2]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h₀ : a * b > 0)
  (h₁ : a⁻¹ > b⁻¹) :
-- imply
  a < b := by
-- proof
  obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ := AndGtS_0.ou.AndLtS_0.of.Mul.gt.Zero h₀
  ·
    apply Lt.of.LtInvS.Lt0.Lt0
    repeat assumption
  ·
    apply Lt.of.LtInvS.Gt0.Gt0
    repeat assumption


-- created on 2025-12-08
