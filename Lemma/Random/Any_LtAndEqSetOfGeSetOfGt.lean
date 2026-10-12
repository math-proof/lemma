import Mathlib.Data.Fintype.Basic
import Mathlib.Basic.Real.Basic
import sympy.Basic
import Lemma.Random.Any_LtAndEqSetOfLeSetOfLt
open Random


@[path]
private lemma main
  [Fintype Ω]
-- given
  (X : Ω → ℝ)
  (t : ℝ) :
-- imply
  ∃ q, q < t ∧ {ω | t ≤ X ω} = {ω | q < X ω} := by
-- proof
  obtain ⟨q, hq, h⟩ := Any_LtAndEqSetOfLeSetOfLt (-X) (-t)
  refine ⟨-q, by linarith, Set.ext fun ω => ?_⟩
  have := Set.ext_iff.mp h ω
  simp only [Set.mem_ofPred_eq, Pi.neg_apply, neg_le_neg_iff] at this ⊢
  rw [this]
  constructor <;>
    intro <;>
    linarith


-- created on 2026-09-26
-- updated on 2026-10-12
