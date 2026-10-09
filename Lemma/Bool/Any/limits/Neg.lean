import Lemma.Bool.Any.of.Any.limits.Neg
open Bool


@[path]
private lemma main
  {f : ℤ → Prop}
  {a b : ℤ} :
-- imply
  (∃ i ∈ Set.Ico a b, f i) ↔ ∃ i ∈ Set.Ico (1 - b) (1 - a), f (-i) :=
-- proof
  ⟨Any.of.Any.limits.Neg, Any.of.Any.limits.Neg.given⟩


-- created on 2019-02-19
