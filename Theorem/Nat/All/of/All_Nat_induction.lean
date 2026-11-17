module

public import Mathlib
public import Abbrev.Analysis.Section_2_1

public section

open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.induction](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
public theorem Nat.All.of.All_Nat_induction
-- given
  (P : Chapter2.Nat → Prop)
  (hbase : P 0)
  (hind : ∀ n, P n → P (n++)) :
-- imply
  ∀ n, P n :=
-- proof
  by
    intro n
    induction n with
    | zero => exact hbase
    | succ n ih => exact hind _ ih


-- created on 2026-10-22
-- updated on 2026-10-26
