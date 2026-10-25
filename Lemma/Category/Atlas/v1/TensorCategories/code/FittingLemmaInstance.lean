import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.FittingLemmaInstance
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents


/--
[idem_trivial_of_indecomposable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FittingLemmaInstance.lean)
-/
@[path]
private lemma idem_trivial_of_indecomposable_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {P : C}
  {e : P ⟶ P}
-- given
  (hP : Indecomposable P)
  (he : e ≫ e = e) :
-- imply
  e = 0 ∨ e = 𝟙 P := by
-- proof
  apply CategoryTheory.idem_trivial_of_indecomposable hP e he


-- created on 2026-10-23
