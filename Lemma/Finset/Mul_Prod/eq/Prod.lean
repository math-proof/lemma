import Lemma.Finset.Prod.eq.MulProdS
import Lemma.Set.Ico.eq.SDiffRangeS
import Lemma.Set.In_Ico
import Lemma.Set.EqInterSingleton.of.In
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Finset.Ico.eq.SDiffIco
open Set Finset Nat


@[main]
private lemma main
  [Fintype ℕ]
  [CommMonoid α]
-- given
  (f : ℕ → α)
  (i : Fin n) :
-- imply
  f i * ∏ k ∈ Finset.Ico ((i : ℕ) + 1) n, f k = ∏ k ∈ Finset.Ico (i : ℕ) n, f k := by
-- proof
  rw [Prod.eq.MulProdS (Finset.Ico (i : ℕ) n) {(i : ℕ)} f]
  simp
  apply EqMulS.of.Eq.left
  congr
  apply Ico.eq.SDiffIco


-- created on 2025-05-18
