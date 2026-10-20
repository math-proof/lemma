import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Convex.Kirchberger
open MetaMathlibExt


/--
[kirchberger](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/Kirchberger.lean)
-/
@[path]
private lemma kirchberger_eq
  :
-- imply
  ∀ (d : ℕ) (A B : Finset (EuclideanSpace ℝ (Fin d))),
    (∃ w : EuclideanSpace ℝ (Fin d), ∃ b : ℝ,
    w ≠ 0 ∧ (∀ a ∈ A, inner ℝ w a < b) ∧ (∀ c ∈ B, b < inner ℝ w c)) ↔
    ∀ C : Finset (EuclideanSpace ℝ (Fin d)), C ⊆ A ∪ B → C.card ≤ d + 2 →
    ∃ w : EuclideanSpace ℝ (Fin d), ∃ b : ℝ,
    w ≠ 0 ∧ (∀ a ∈ A ∩ C, inner ℝ w a < b) ∧
    (∀ c ∈ B ∩ C, b < inner ℝ w c) := by
-- proof
  apply MetaMathlibExt.kirchberger


-- created on 2026-10-20
