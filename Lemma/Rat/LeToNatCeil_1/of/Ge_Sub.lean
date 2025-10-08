import Lemma.Algebra.GeAdd.of.Ge_Sub
import Lemma.Rat.LeToNatCeil_1.of.Le_Add
open Algebra Rat


@[main]
private lemma main
  {start stop step : ℕ}
-- given
  (h : stop ≥ start - step) :
-- imply
  ⌈(start - stop : ℚ) / step⌉.toNat ≤ 1 := by
-- proof
  have h:= GeAdd.of.Ge_Sub.nat h
  apply LeToNatCeil_1.of.Le_Add h


-- created on 2025-05-28
