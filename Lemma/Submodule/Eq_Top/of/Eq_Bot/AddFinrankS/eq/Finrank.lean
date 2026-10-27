import Mathlib
import Initialize.Tactic.Attr.Basic
open Module


/--
[sup_eq_top_of_finrank_add_eq_and_inf_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/DirectSum.lean)
-/
@[path]
private lemma main
  [DivisionRing F]
  [AddCommGroup V]
  [Module F V]
  [FiniteDimensional F V]
  {W W' : Submodule F V}
-- given
  (hdim : finrank F W + finrank F W' = finrank F V)
  (hinter : W ⊓ W' = ⊥) :
-- imply
  W ⊔ W' = ⊤ := by
-- proof
  apply Submodule.eq_top_of_disjoint W W' (le_of_eq hdim.symm) (disjoint_iff.mpr hinter)


-- created on 2026-10-23
-- updated on 2026-10-26
