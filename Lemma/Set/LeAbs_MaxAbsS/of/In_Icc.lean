import Lemma.Int.GeAbs
import Lemma.Int.LeAbs.is.LeNeg.Le
import Lemma.Int.LeNegAbs
import Lemma.Nat.Ge.of.Ge.Ge
import Lemma.Nat.GeMax
import Lemma.Nat.Le.of.Le.Le
import Lemma.Set.In_Icc.is.Le.Le
open Set Int Nat


@[main]
private lemma main
  [AddCommGroup α]
  [LinearOrder α]
  [IsOrderedAddMonoid α]
  {a b : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  |x| ≤ |a| ⊔ |b| := by
-- proof
  obtain ⟨ha, hb⟩ := Le.Le.of.In_Icc h
  apply LeAbs.of.LeNeg.Le
  .
    apply (ge_trans (ge_trans ha (LeNegAbs a)) (neg_le_neg (GeMax.left |a| |b|)))
  .
    apply (le_trans hb (le_trans (GeAbs b) (GeMax |a| |b|)))


-- created on 2018-06-30
