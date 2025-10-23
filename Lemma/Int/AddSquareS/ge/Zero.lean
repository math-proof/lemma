import Lemma.Int.GeSquare_0
import Lemma.Nat.Add.ge.Zero.of.Ge_0.Ge_0
open Nat Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α} :
-- imply
  a² + b² ≥ 0 := by
-- proof
  have hₐ := GeSquare_0 (a := a)
  have h_b := GeSquare_0 (a := b)
  have := Add.ge.Zero.of.Ge_0.Ge_0 hₐ h_b
  assumption


-- created on 2025-01-16
