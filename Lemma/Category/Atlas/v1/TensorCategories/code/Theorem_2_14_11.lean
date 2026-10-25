import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.DualCategory.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.DualCategory
open CategoryTheory in


/--
[Theorem_2_14_11](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_2_14_11.lean)
-/
@[path]
lemma Theorem_2_14_11
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  [ExactModuleCategory C M]
  [inst : LeftModuleCategory (DualCatObj C M) M] :
-- imply
  (∀ (M₁ : Type u) [Category.{v} M₁] [ExactModuleCategory C M₁] [Category.{v} (ModuleFunctor C M₁ M)], ∃ (_ : ExactModuleCategory (DualCatObj C M) (ModuleFunctor C M₁ M)) (Ψ_Φ_M₁ : Type (max u v)) (_ : Category.{v} Ψ_Φ_M₁) (_ : ExactModuleCategory C Ψ_Φ_M₁), Nonempty (ModuleEquivalence C Ψ_Φ_M₁ M₁)) ∧ (∀ (M₂ : Type u) [Category.{v} M₂] [ExactModuleCategory (DualCatObj C M) M₂] [Category.{v} (ModuleFunctor (DualCatObj C M) M₂ M)], ∃ (_ : ExactModuleCategory C (ModuleFunctor (DualCatObj C M) M₂ M)) (Φ_Ψ_M₂ : Type (max u v)) (_ : Category.{v} Φ_Ψ_M₂) (_ : ExactModuleCategory (DualCatObj C M) Φ_Ψ_M₂), Nonempty (ModuleEquivalence (DualCatObj C M) Φ_Ψ_M₂ M₂)) :=
-- proof
  ⟨fun M₁ => DualCatObj.morita_equivalence_forward M₁,
    fun M₂ => DualCatObj.morita_equivalence_backward M₂⟩


-- created on 2026-10-23
