import sympy.sets.sets
import Lemma.Algebra.Prod.eq.MulProdS
import Lemma.Set.Ico.eq.SDiffRangeS
import Lemma.Set.In_Ico
import Lemma.Set.EqInterSingleton.of.In
import Lemma.Algebra.EqMulS.of.Eq
import Lemma.Set.Ico.eq.SDiffIco
open Algebra Set


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
  apply Ico.eq.SDiffIco.fin


-- created on 2025-05-18
