/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Convex/KKM.lean -/

-- Author: @toskua, Avocado
-- Original focused tests by @akiezun in d855ffa90ad200e1ae118101768bd192d0d3c59f.
-- @toskua, Avocado migrated only the representation to Convexity.StdSimplex.

import Theorem.Analysis.Convex.KKM.Part4
open MathlibExt.Analysis.Convex.KKM

/-!
# Tests for the Knaster–Kuratowski–Mazurkiewicz lemma

Focused API checks for `MathlibExt.Analysis.Convex.KKM.kkm_lemma`:
the exact generic signature applies as stated, and the zero-dimensional
(`n = 0`) boundary case holds for the trivial one-piece closed cover.
-/


/-- The generic `kkm_lemma` signature applies as stated. -/
example {n : ℕ}
    (F : Fin (n + 1) → Set (Convexity.StdSimplex ℝ (Fin (n + 1))))
    (hF_closed : ∀ i, IsClosed (F i))
    (hF_cover : ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∃ i : Fin (n + 1), 0 < x.weights i ∧ x ∈ F i) :
    ∃ x : Convexity.StdSimplex ℝ (Fin (n + 1)), ∀ i, x ∈ F i :=
  kkm_lemma F hF_closed hF_cover

/-- Zero-dimensional boundary case: with a single vertex, the trivial
one-piece closed cover has a common point. -/
example :
    ∃ x : Convexity.StdSimplex ℝ (Fin 1),
      ∀ _i : Fin 1, x ∈ (Set.univ : Set (Convexity.StdSimplex ℝ (Fin 1))) := by
  refine kkm_lemma ((fun _ => Set.univ) : Fin 1 → Set (Convexity.StdSimplex ℝ (Fin 1))) ?_ ?_
  · intro _i
    exact isClosed_univ
  · intro x
    refine ⟨0, ?_, Set.mem_univ _⟩
    have h0 : x.weights 0 = 1 := by
      have h := x.total_of_fintype
      rwa [Fin.sum_univ_one] at h
    rw [h0]
    exact one_pos

