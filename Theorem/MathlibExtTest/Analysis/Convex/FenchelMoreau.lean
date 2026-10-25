/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Convex/FenchelMoreau.lean -/


import Theorem.Analysis.Convex.FenchelMoreau.Part2
/-!
# Tests for Fenchel conjugates and the Fenchel–Moreau theorem

Focused API checks: the stronger `fenchel_moreau` signature applies without
a `T2Space` hypothesis, the conjugate/biconjugate unfold to their defining
suprema, and `isClosed_epi_real` applies under its minimal hypotheses.
-/


noncomputable section

namespace FenchelMoreauTest

open MathlibExt.Analysis.Convex.FenchelMoreau

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E]

/-- The conjugate unfolds to its defining supremum. -/
example (f : E → EReal) (L : E →L[ℝ] ℝ) :
    fenchelConj f L = ⨆ y : E, (((L y : ℝ)) : EReal) - f y := rfl

/-- The biconjugate unfolds to a supremum over dual elements. -/
example (f : E → EReal) (x : E) :
    fenchelBiconj f x
      = ⨆ L : E →L[ℝ] ℝ, (((L x : ℝ)) : EReal) - fenchelConj f L := rfl

/-- Easy direction: the biconjugate never exceeds `f`. -/
example (f : E → EReal) (hf_not_bot : ∀ x, f x ≠ ⊥) (x : E) :
    fenchelBiconj f x ≤ f x :=
  biconj_le f hf_not_bot x

/-- The closed-epigraph API needs only lower semicontinuity. -/
example {G : Type*} [TopologicalSpace G] (f : G → EReal)
    (hf_lsc : LowerSemicontinuous f) :
    IsClosed {p : G × ℝ | f p.1 ≤ (p.2 : EReal)} :=
  isClosed_epi_real f hf_lsc

section NoT2Space

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]

/-- `fenchel_moreau` applies without a `T2Space F` hypothesis. -/
example {f : F → EReal}
    (hf_convex : Convex ℝ {p : F × ℝ | f p.1 ≤ (p.2 : EReal)})
    (hf_lsc : LowerSemicontinuous f)
    (hf_not_top : ∃ x, f x ≠ ⊤)
    (hf_not_bot : ∀ x, f x ≠ ⊥) :
    ∀ x : F,
      f x = ⨆ (L : F →L[ℝ] ℝ),
        (((L x : ℝ) : EReal) - (⨆ y : F, ((L y : ℝ) : EReal) - f y)) :=
  fenchel_moreau hf_convex hf_lsc hf_not_top hf_not_bot

end NoT2Space
end FenchelMoreauTest
end
