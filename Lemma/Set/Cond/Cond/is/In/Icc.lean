import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y b : ℝ} :
-- imply
  x < y ∧ x > b ↔ x ∈ Set.Ioo b y := by
-- proof
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩


@[path]
private lemma left_close
  {x y b : ℝ} :
-- imply
  x < y ∧ x ≥ b ↔ x ∈ Set.Ico b y := by
-- proof
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩


-- created on 2022-01-07
