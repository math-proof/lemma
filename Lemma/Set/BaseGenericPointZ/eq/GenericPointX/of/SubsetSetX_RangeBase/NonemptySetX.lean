import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_base_genericPoint_eq_genericPoint_of_subset_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_base_genericPoint_eq_genericPoint_of_subset_range.lean)
-/
@[path]
private lemma main
  {Z X : Scheme.{u}} [IrreducibleSpace ↥Z] [IsIntegral X]
  {q : Z ⟶ X}
  {U : X.Opens}
-- given
  (hU : (U : Set ↥X).Nonempty)
  (hsub : (U : Set ↥X) ⊆ Set.range q.base) :
-- imply
  q.base (genericPoint ↥Z) = genericPoint ↥X := by
-- proof
  have h1 : IsGenericPoint (q.base (genericPoint ↥Z)) (closure (q.base '' (⊤ : Set ↥Z))) :=
    (genericPoint_spec ↥Z).image q.continuous
  have hdense : closure (q.base '' (⊤ : Set ↥Z)) = (⊤ : Set ↥X) := by
    apply Set.eq_univ_of_univ_subset
    have hUd : Dense (U : Set ↥X) := U.isOpen.dense hU
    rw [← hUd.closure_eq]
    apply closure_minimal _ isClosed_closure
    refine hsub.trans ?_
    rw [Set.top_eq_univ, Set.image_univ]
    exact subset_closure
  rw [hdense] at h1
  exact h1.eq (genericPoint_spec ↥X)


-- created on 2026-10-05
