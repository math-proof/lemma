import Lemma.Set.EqUnionS.of.Eq.Eq
import Lemma.Set.EqCupIn_Singleton
import Lemma.Set.UnionCupS.eq.CupIn_Union
import Lemma.Set.Icc.eq.UnionIco.of.Le
open Set


@[main]
private lemma main
  [PartialOrder α]
  {g f : α → Set α}
  {a b : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : g b = f b)
  (h₂ : ⋃ k ∈ Ico a b, g k = ⋃ k ∈ Ico a b, f k) :
-- imply
  ⋃ k ∈ Icc a b, g k = ⋃ k ∈ Icc a b, f k := by
-- proof
  have := EqUnionS.of.Eq.Eq h₂ h₁
  have h_gb := EqCupIn_Singleton g b
  have h_fb := EqCupIn_Singleton f b
  rw [← h_gb, ← h_fb] at this
  repeat rw [UnionCupS.eq.CupIn_Union] at this
  rwa [← Icc.eq.UnionIco.of.Le h₀] at this


-- created on 2025-07-20
-- updated on 2025-07-21
