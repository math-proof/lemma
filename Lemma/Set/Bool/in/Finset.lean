import Lemma.Bool.Bool.eq.Ite
import Lemma.Set.InIte.is.OrAndS
import Lemma.Bool.Or_Not
open Set Bool


@[main]
private lemma main
  [Decidable p] :
-- imply
  (Bool.toNat p) ∈ ({0, 1} : Set ℕ) := by
-- proof
  rw [Bool.eq.Ite (p := p)]
  apply InIte.of.OrAndS
  simp
  apply Or_Not


-- created on 2025-04-20
