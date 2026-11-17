import Abbrev.Analysis.Section_2_1
import Theorem.Nat.Zero.eq.One
import Theorem.Nat.One.eq.Two
import Theorem.Nat.Two.eq.Three
import Theorem.Nat.Ne0
import Theorem.Nat.Four.ne.Zero
import Theorem.Nat.Eq.of.Eq_Nat_succ_cancel
import Theorem.Nat.Ne_Nat_succ_ne_succ
import Theorem.Nat.Six.ne.Two
import Theorem.Nat.Ne62
import Theorem.Nat.All.of.All_Nat_induction
import Theorem.Nat.EqRecurseNat0
import Theorem.Nat.EqRecurse
import Theorem.Nat.EqAndAll_Eq.is.Eq_Recurse
import Theorem.Nat.All_Eq.Unique


namespace Chapter2

abbrev Nat.zero_succ : (0 : Nat)++ = 1 := _root_.Nat.Zero.eq.One

abbrev Nat.one_succ : (1 : Nat)++ = 2 := _root_.Nat.One.eq.Two

abbrev Nat.two_succ : (2 : Nat)++ = 3 := _root_.Nat.Two.eq.Three

abbrev Nat.succ_ne (n : Nat) : n++ ≠ 0 := _root_.Nat.Ne0

abbrev Nat.four_ne : (4 : Nat) ≠ 0 := _root_.Nat.Four.ne.Zero

abbrev Nat.succ_cancel {n m : Nat} (hnm : n++ = m++) : n = m := _root_.Nat.Eq.of.Eq_Nat_succ_cancel hnm

abbrev Nat.succ_ne_succ (n m : Nat) : n ≠ m → n++ ≠ m++ := _root_.Nat.Ne_Nat_succ_ne_succ

abbrev Nat.six_ne_two : (6 : Nat) ≠ 2 := _root_.Nat.Six.ne.Two

abbrev Nat.six_ne_two' : (6 : Nat) ≠ 2 := _root_.Nat.Ne62

abbrev Nat.induction (P : Nat → Prop) (hbase : P 0) (hind : ∀ n, P n → P (n++)) : ∀ n, P n :=
  _root_.Nat.All.of.All_Nat_induction P hbase hind

abbrev Nat.recurse_zero (f : Nat → Nat → Nat) (c : Nat) : Nat.recurse f c 0 = c := _root_.Nat.EqRecurseNat0

abbrev Nat.recurse_succ (f : Nat → Nat → Nat) (c n : Nat) : recurse f c (n++) = f n (recurse f c n) :=
  _root_.Nat.EqRecurse

abbrev Nat.eq_recurse (f : Nat → Nat → Nat) (c : Nat) (a : Nat → Nat) :
    (a 0 = c ∧ ∀ n, a (n++) = f n (a n)) ↔ a = recurse f c :=
  _root_.Nat.EqAndAll_Eq.is.Eq_Recurse

abbrev Nat.recurse_uniq (f : Nat → Nat → Nat) (c : Nat) :
    ∃! (a : Nat → Nat), a 0 = c ∧ ∀ n, a (n++) = f n (a n) :=
  _root_.Nat.All_Eq.Unique

end Chapter2
