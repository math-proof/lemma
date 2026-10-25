import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.Corollary_1_48_3
open CategoryTheory MonoidalCategory


namespace CategoryTheory

/--
[Corollary_1_48_3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_48_3.lean)
-/
@[path]
lemma Corollary_1_48_3
  {k : Type u}
  [Field k] :
-- imply
  (∀ {C : Type u} [Category.{u} C] [MonoidalCategory C] [Abelian C] [EnoughProjectives C] [Linear k C] [RigidCategory C] (d : FPdimFunction (C := C)), d.IsIntegral → ∃ (H : Type u) (_ : Ring H) (_ : Algebra k H) (_ : QuasiHopfAlgebra k H) (_ : FiniteDimensional k H), Nonempty (C ≌ QuasiRepCat k H)) ∧ (∀ (H₁ : Type u) [Ring H₁] [Algebra k H₁] [QuasiHopfAlgebra k H₁] [FiniteDimensional k H₁] (H₂ : Type u) [Ring H₂] [Algebra k H₂] [QuasiHopfAlgebra k H₂] [FiniteDimensional k H₂], QuasiHopfTwistIsoEquiv k H₁ H₂ → QuasiRepCatMonoidalEquiv k H₁ H₂) ∧ (∀ (H₁ : Type u) [Ring H₁] [Algebra k H₁] [QuasiHopfAlgebra k H₁] [FiniteDimensional k H₁] (H₂ : Type u) [Ring H₂] [Algebra k H₂] [QuasiHopfAlgebra k H₂] [FiniteDimensional k H₂], QuasiRepCatMonoidalEquiv k H₁ H₂ → QuasiHopfTwistIsoEquiv k H₁ H₂) := by
-- proof
  refine ⟨?_, ?_, ?_⟩
  ·
    intro C _ _ _ _ _ _ d hint
    exact integral_exists_quasiHopf_rep k d hint
  ·
    intro H₁ _ _ _ _ H₂ _ _ _ _ hte
    exact twist_equiv_imp_quasiRepCat_equiv k H₁ H₂ hte
  ·
    intro H₁ _ _ _ _ H₂ _ _ _ _ ⟨e⟩
    exact quasiRepCat_equiv_imp_twist_equiv k H₁ H₂ e

end CategoryTheory


-- created on 2026-10-23
