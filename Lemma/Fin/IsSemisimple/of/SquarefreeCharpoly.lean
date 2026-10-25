import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraNotes.code.Diagonalization
open Matrix Diagonalization
open Module Polynomial


/--
[isSemisimple_of_squarefree_charpoly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Diagonalization.lean)
-/
@[path]
private lemma main
  [Field K]
  [AddCommGroup V]
  [Module K V]
  [FiniteDimensional K V]
  {f : End K V}
-- given
  (hsq : Squarefree f.charpoly) :
-- imply
  f.IsSemisimple :=
-- proof
  End.isSemisimple_of_squarefree_aeval_eq_zero hsq f.aeval_self_charpoly



/--
[isSemisimple_of_charpoly_eq_prod_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Diagonalization.lean)
-/
private lemma isSemisimple_of_charpoly_eq_prod_distinct
  [Field K]
  [AddCommGroup V]
  [Module K V]
  [FiniteDimensional K V]
  {f : End K V}
  [Fintype ι]
  {μ : ι → K}
-- given
  (hμ : Function.Injective μ)
  (hprod : f.charpoly = ∏ i, (X - C (μ i))) :
-- imply
  f.IsSemisimple := by
-- proof
  apply isSemisimple_of_squarefree_charpoly
  rw [hprod]
  exact (separable_prod_X_sub_C_iff.mpr hμ).squarefree
open Matrix



-- created on 2026-10-23
-- updated on 2026-10-24
