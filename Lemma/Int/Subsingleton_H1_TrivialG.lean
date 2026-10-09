import Mathlib
import sympy.Basic

open CategoryTheory groupCohomology
open Rep.FiniteCyclicGroup

/--
[groupCohomology_subsingleton_H1_trivial_int](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_subsingleton_H1_trivial_int.lean)
-/
@[path]
private lemma main
  [Group G] [Finite G] :
-- imply
  Subsingleton (H1 (Rep.trivial ℤ G ℤ)) := by
-- proof
  have : Subsingleton (Additive G →+ ℤ) := by
    refine ⟨fun f₁ f₂ => AddMonoidHom.ext fun x => ?_⟩
    have h : ∀ f : Additive G →+ ℤ, f x = 0 := fun f => by
      have h1 : (Nat.card (Additive G)) • f x = 0 := by
        rw [← map_nsmul, card_nsmul_eq_zero', map_zero]
      rcases (by simpa [nsmul_eq_mul] using h1 : Nat.card (Additive G) = 0 ∨ f x = 0) with h2 | h2
      · exact absurd h2 Nat.card_pos.ne'
      · exact h2
    rw [h f₁, h f₂]
  exact (H1IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).toLinearEquiv.toEquiv.subsingleton


-- created on 2026-10-05
