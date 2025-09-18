import Lemma.Set.AllIn_SDiff.of.All
import Lemma.Set.Icc.eq.SDiffIoc.Lt
open Set


@[main]
private lemma main
  [LinearOrder α]
  {f : α → Prop}
  {c a : α}
-- given
  (h₀ : a < c)
  (h₁ : ∀ x ∈ Ioc a b, f x) :
-- imply
  ∀ x ∈ Icc c b, f x := by
-- proof
  rw [Icc.eq.SDiffIoc.Lt h₀]
  apply AllIn_SDiff.of.All h₁ (Ioo a c)


-- created on 2025-07-19
