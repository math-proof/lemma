import Lemma.Rat.SubDivS.eq.DivMul_Sub.of.Ne_0.Ne_0
open Rat


@[main]
private lemma main
  [Field α]
  {a b : α}
-- given
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0) :
-- imply
  1 / a - 1 / b = (b - a) / (a * b) := by
-- proof
  simpa using SubDivS.eq.DivMul_Sub.of.Ne_0.Ne_0 (x := (1 : α)) h₀ h₁


-- created on 2018-07-21
