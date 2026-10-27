import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b c lo hi : ℝ}
-- given
  (h₀ : a < 0)
  (h₁ : -b / (2 * a) ∈ Set.Icc lo hi) :
-- imply
  -b / (2 * a) ∈ Set.Icc lo hi ∧
    ∀ x ∈ Set.Icc lo hi, a * x ^ 2 + b * x + c ≤ c - b ^ 2 / (4 * a) := by
-- proof
  refine ⟨h₁, ?_⟩
  intro x _
  have hsq : a * x ^ 2 + b * x + c - (c - b ^ 2 / (4 * a)) =
      (2 * a * x + b) ^ 2 / (4 * a) := by
    field_simp [h₀.ne]
    ring
  have hle : (2 * a * x + b) ^ 2 / (4 * a) ≤ 0 :=
    div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
  linarith [hsq, hle]


-- created on 2019-12-26
-- updated on 2026-10-26
