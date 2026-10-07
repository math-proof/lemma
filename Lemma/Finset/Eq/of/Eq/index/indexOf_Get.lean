import sympy.tensor.index_of
import sympy.sets.sets
import sympy.Basic
import Lemma.Nat.EqIndexGet.of.Lt.InjOnRange


@[main]
private lemma main
  {n j : ℕ}
  {x : ℕ → ℤ}
-- given
  (h : (Finset.range n).image x = Finset.Ico 0 (n : ℤ))
  (hj : j < n) :
-- imply
  IndexOf.index (x j) x n = j := by
-- proof
  have hc : ((Finset.range n).image x).card = (Finset.range n).card := by
    rw [h, Int.card_Ico, Finset.card_range]
    omega
  exact Nat.EqIndexGet.of.Lt.InjOnRange x n (Finset.card_image_iff.mp hc) hj


-- created on 2020-10-25
