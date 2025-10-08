import Lemma.Bool.Bool.eq.Ite
import Lemma.Algebra.Pow_Ite.eq.Ite_PowS
open Algebra Bool


@[main]
private lemma main
  [Fintype ι] [DecidableEq ι]
  [CommMonoid α]
  {f : ι → α} :
-- imply
  ∏ i ∈ s, f i = ∏ i ∈ Set.univ, f i ^ Bool.toNat (i ∈ s) := by
-- proof
  simp only [Bool.eq.Ite]
  simp only [Pow_Ite.eq.Ite_PowS]
  simp


-- created on 2025-04-29
-- updated on 2025-04-30
