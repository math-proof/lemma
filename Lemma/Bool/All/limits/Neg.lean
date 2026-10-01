import Lemma.Bool.All.of.All.limits.Neg
open Bool


@[main]
private lemma main
  {f : ℤ → Prop}
  {a b : ℤ} :
-- imply
  (∀ i ∈ Set.Ico a b, f i) ↔ ∀ i ∈ Set.Ico (1 - b) (1 - a), f (-i) :=
-- proof
  ⟨All.of.All.limits.Neg, All.of.All.limits.Neg.given⟩


-- created on 2018-12-19
