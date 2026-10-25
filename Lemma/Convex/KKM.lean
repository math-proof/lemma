import Mathlib
import sympy.Basic
import Theorem.Analysis.Convex.KKM.Part4

/--
[KKM](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/KKM.lean)
-/
@[path]
private lemma kkm_lemma_is
-- given
  {n : ℕ}
  (F : Fin (n + 1) → Set (Convexity.StdSimplex ℝ (Fin (n + 1))))
  (hF_closed : ∀ i, IsClosed (F i))
  (hF_cover : ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
    ∃ i : Fin (n + 1), 0 < x.weights i ∧ x ∈ F i) :
-- imply
  ∃ x : Convexity.StdSimplex ℝ (Fin (n + 1)), ∀ i, x ∈ F i := by
-- proof
  apply Convex.KKM.kkm_lemma F hF_closed hF_cover

-- created on 2026-10-10
