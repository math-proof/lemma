import Mathlib
import sympy.Basic

open TrivSqZeroExt DualNumber

/--
[TrivSqZeroExt_isLocalRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_TrivSqZeroExt_isLocalRing.lean)
-/
@[path]
private lemma main
  [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [IsLocalRing R] :
-- imply
  IsLocalRing (TrivSqZeroExt R M) := by
-- proof
  have : Nontrivial (TrivSqZeroExt R M) := (TrivSqZeroExt.inl_injective (R := R) (M := M)).nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst with h | h
  · exact Or.inl (isUnit_iff_isUnit_fst.2 h)
  · refine Or.inr (isUnit_iff_isUnit_fst.2 ?_)
    rwa [fst_sub, fst_one]


-- created on 2026-10-03
