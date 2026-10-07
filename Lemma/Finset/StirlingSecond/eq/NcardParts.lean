import sympy.sets.stirling_partition
import sympy.Basic
import Lemma.Finset.NcardParts0'0.eq.One
import Lemma.Finset.NcardParts0_Add_1.eq.Zero
import Lemma.Finset.NcardParts_Add_1'0.eq.Zero
import Lemma.Finset.NcardParts_Add_1_Add_1.eq.AddNcardPartsMulAdd_1NcardParts
open Finset Stirling.conditionset


@[main]
private lemma main
-- given
  (n k : ℕ) :
-- imply
  Nat.stirlingSecond n k = (parts n k).ncard := by
-- proof
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rw [NcardParts0'0.eq.One, Nat.stirlingSecond_zero]
    | succ k => rw [NcardParts0_Add_1.eq.Zero, Nat.stirlingSecond_zero_succ]
  | succ n ih =>
    cases k with
    | zero => rw [NcardParts_Add_1'0.eq.Zero, Nat.stirlingSecond_succ_zero]
    | succ k =>
      rw [Nat.stirlingSecond_succ_succ, NcardParts_Add_1_Add_1.eq.AddNcardPartsMulAdd_1NcardParts, ← ih, ← ih]
      ring


-- created on 2026-10-07
