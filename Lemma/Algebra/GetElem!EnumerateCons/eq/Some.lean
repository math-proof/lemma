import stdlib.List
import sympy.Basic


@[main]
private lemma main
  {head : α}
  {tail : List α} :
-- imply
  (head :: tail).enumerate[0]? = some ⟨⟨0, by simp⟩, head⟩ := by
-- proof
  simp [List.enumerate]


-- created on 2025-06-02
