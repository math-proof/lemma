import Lemma.Bool.Any.of.Any_And
import Lemma.Bool.Cond.of.Any
open Bool


@[main, comm, mp, mpr]
private lemma main
  {r :Prop}
  {p : α → Prop} :
-- imply
  (∃ x : α, p x ∧ r) ↔ (∃ x : α, p x) ∧ r := by
-- proof
  constructor <;>
    intro h
  .
    exact ⟨
      Any.of.Any_And.left h,
      Cond.of.Any (
        Any.of.Any_And h)
    ⟩
  .
    let ⟨⟨x, hLeft⟩, hRight⟩ := h
    exact ⟨x, hLeft, hRight⟩


-- created on 2024-07-01
