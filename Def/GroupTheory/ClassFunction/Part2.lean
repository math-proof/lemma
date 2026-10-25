/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Group.Conj
import Theorem.GroupTheory.ClassFunction


namespace MathlibExt.GroupTheory.ClassFunctionWanted

/-- Class functions are linearly equivalent to functions on conjugacy classes. -/
def classFunctionsEquivConjClasses (G : Type*) [Group G] (k : Type*) [Field k] :
    classFunctions G k ≃ₗ[k] (ConjClasses G → k) where
  toFun f := Quotient.lift f fun _ _ => f.property.eq_of_isConj
  invFun q :=
    ⟨q ∘ ConjClasses.mk,
      (isClassFunction_iff_factor_conjClasses _).2 ⟨q, fun _ => rfl⟩⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    rfl
  right_inv q := by
    funext c
    refine Quotient.inductionOn c ?_
    intro x
    rfl
  map_add' f g := by
    funext c
    refine Quotient.inductionOn c ?_
    intro x
    rfl
  map_smul' a f := by
    funext c
    refine Quotient.inductionOn c ?_
    intro x
    rfl

end MathlibExt.GroupTheory.ClassFunctionWanted
