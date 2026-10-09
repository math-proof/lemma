import Mathlib
import sympy.Basic
import sympy.Analysis.Convex.FenchelMoreau

open Convex.FenchelMoreau

/-- [isClosed_epi_real](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/FenchelMoreau.lean) -/
@[path]
private lemma isClosed_epi_real_eq
-- given
  {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E]
  (f : E → EReal)
  (hf_lsc : LowerSemicontinuous f) :
-- imply
  IsClosed {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
-- proof
  apply isClosed_epi_real f hf_lsc

/-- [biconj_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/FenchelMoreau.lean) -/
@[path]
private lemma biconj_le_eq
-- given
  {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E]
  (f : E → EReal)
  (hf_not_bot : ∀ x, f x ≠ ⊥)
  (x : E) :
-- imply
  fenchelBiconj f x ≤ f x := by
-- proof
  apply biconj_le f hf_not_bot x

/-- [fenchel_moreau](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/FenchelMoreau.lean) -/
@[path]
private lemma fenchel_moreau_eq
-- given
  {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E]
  {f : E → EReal}
  (hf_convex : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)})
  (hf_lsc : LowerSemicontinuous f)
  (hf_not_top : ∃ x, f x ≠ ⊤)
  (hf_not_bot : ∀ x, f x ≠ ⊥) :
-- imply
  ∀ x : E,
    f x = ⨆ (L : E →L[ℝ] ℝ),
      (((L x : ℝ) : EReal) - (⨆ y : E, ((L y : ℝ) : EReal) - f y)) := by
-- proof
  apply fenchel_moreau hf_convex hf_lsc hf_not_top hf_not_bot

-- created on 2026-10-10
