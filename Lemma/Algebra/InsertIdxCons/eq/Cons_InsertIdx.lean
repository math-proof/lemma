import Lemma.Basic


@[main]
private lemma main
-- given
  (v : List α)
  (x v₀ : α)
  (n : ℕ) :
-- imply
  (v₀ :: v).insertIdx (n + 1) x = v₀ :: v.insertIdx n x := by
-- proof
  cases n <;> rfl


-- created on 2025-06-09
