/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/ClassFunction.lean -/


import sympy.atlas.GroupTheory.ClassFunction
import Lemma.Fin.IsClassFunctionCharacter
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite

open MathlibExt.GroupTheory.ClassFunctionWanted

-- Every function on this finite abelian group factors and is constant on conjugate elements.
example (f : Multiplicative (ZMod 3) → ℚ) (x y : Multiplicative (ZMod 3))
    (hxy : IsConj x y) : IsClassFunction f ∧ f x = f y := by
  have hf : IsClassFunction f := by
    rw [isClassFunction_iff_factor_conjClasses]
    let e := ConjClasses.mkEquiv (α := Multiplicative (ZMod 3))
    let q : ConjClasses (Multiplicative (ZMod 3)) → ℚ := f ∘ e.symm
    refine ⟨classFunctionsEquivConjClasses _ ℚ
      ((classFunctionsEquivConjClasses _ ℚ).symm q), ?_⟩
    intro z
    rw [classFunctionsEquivConjClasses_apply_mk,
      classFunctionsEquivConjClasses_symm_apply]
    exact congrArg f (e.symm_apply_apply z).symm
  exact ⟨hf, hf.eq_of_isConj hxy⟩

-- The class-function space on the two-element abelian group has dimension two.
example : Module.finrank ℚ ↥(classFunctions (Multiplicative (ZMod 2)) ℚ) = 2 := by
  rw [finrank_classFunctions_eq_card_conjClasses]
  calc
    Nat.card (ConjClasses (Multiplicative (ZMod 2))) =
        Nat.card (Multiplicative (ZMod 2)) :=
      (Nat.card_congr (ConjClasses.mkEquiv (α := Multiplicative (ZMod 2)))).symm
    _ = 2 := by simp
