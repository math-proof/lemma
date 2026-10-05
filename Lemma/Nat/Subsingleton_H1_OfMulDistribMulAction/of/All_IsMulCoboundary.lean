import Mathlib
import sympy.Basic

open groupCohomology

/--
[groupCohomology_subsingleton_H1_ofMulDistribMulAction](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_subsingleton_H1_ofMulDistribMulAction.lean)
-/
@[main]
private lemma main
  {G V : Type} [Group G] [CommGroup V] [MulDistribMulAction G V]
-- given
  (h : ∀ f : G → V, IsMulCocycle₁ f → IsMulCoboundary₁ f) :
-- imply
  Subsingleton (H1 (Rep.ofMulDistribMulAction G V)) := by
-- proof
  refine subsingleton_of_forall_eq 0 fun a => H1_induction_on a fun x => (H1π_eq_zero_iff x).2 ?_

  refine (coboundariesOfIsMulCoboundary₁ ?_).2
  exact h _ (isMulCocycle₁_of_mem_cocycles₁ _ x.2)


-- created on 2026-10-05
