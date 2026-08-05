import Lemma.Finset.Insert_Ico.eq.Ico_Add_1
open Finset Int


@[main]
private lemma main
-- given
  (a : ℤ)
  (n : ℕ) :
-- imply
  (Finset.range n).map (Nat.castEmbedding.trans (addLeftEmbedding a)) = Finset.Ico a (a + n) := by
-- proof
  induction n with
  | zero =>
    simp [Nat.castEmbedding, addLeftEmbedding]
  | succ n ih =>
    simp [Finset.range_add_one, Finset.map_insert]
    rw [ih]
    have h : a ≤ a + n := by omega
    simpa [Nat.cast_add, add_assoc] using Insert_Ico.eq.Ico_Add_1 h


-- created on 2018-04-24
