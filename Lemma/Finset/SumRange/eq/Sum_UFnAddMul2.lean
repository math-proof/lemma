import sympy.sets.fancysets
import Lemma.Finset.SumRange.eq.Sum_UFnMul2.of.Even
import Lemma.Finset.SumRange.eq.Sum_UFnAddMul2.of.Odd
import Lemma.Bool.Cond.of.Imp.ImpNot
import Lemma.Int.Odd.of.Ne_0
import Lemma.Nat.Even.is.Mod_2.eq.Zero
import Lemma.Nat.Odd.is.Mod_2.eq.One
import Lemma.Nat.Even.is.OddAdd_1
import Lemma.Nat.EvenAdd_1.is.Odd
open Finset Nat Int Bool


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (a b : ℤ)
  (f : ℤ → α) :
-- imply
  ∑ n ∈ (Range a b 2).toFinset, f n = ∑ n ∈ Ico (a / 2) ((b + (a + 1) % 2) / 2), f (2 * n + a % 2) := by
-- proof
  apply Cond.of.Imp.ImpNot (p := a % 2 = 0)
  ·
    intro h0
    have h_even : a is even := Even.of.Mod_2.eq.Zero h0
    have h_add : (a + 1) % 2 = 1 := Mod_2.eq.One.of.Odd (OddAdd_1.of.Even h_even)
    rw [SumRange.eq.Sum_UFnMul2.of.Even h_even]
    simp [h0, h_add]
  ·
    intro hne
    have h_odd : a is odd := Odd.of.Ne_0 hne
    have h1 : a % 2 = 1 := Mod_2.eq.One.of.Odd h_odd
    have h_add : (a + 1) % 2 = 0 := Mod_2.eq.Zero.of.Even (EvenAdd_1.of.Odd h_odd)
    rw [SumRange.eq.Sum_UFnAddMul2.of.Odd h_odd]
    simp [h1, h_add]


-- created on 2023-05-30
