import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.limits.domain_defined


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → Prop}
  {g : ℕ → ℕ → Prop} :
-- imply
  (∃ j < n, ∃ i < n, f j ∧ g i j) ↔ ∃ j < n, f j ∧ ∃ i < n, g i j := by
-- proof
  constructor
  ·
    rintro ⟨j, hj, i, hi, hf, hg⟩
    exact ⟨j, hj, hf, i, hi, hg⟩
  ·
    rintro ⟨j, hj, hf, i, hi, hg⟩
    exact ⟨j, hj, i, hi, hf, hg⟩


-- created on 2023-06-06
-- updated on 2026-11-24
