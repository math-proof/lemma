import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.SkewPrimitiveCategorical.Part6
open Coalgebra CategoryTheory MonoidalCategory Category Limits
open scoped TensorProduct
open CategoryTheory MonoidalCategory Category Limits


/--
[trivialSkewPrimitive_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean)
-/
@[path]
lemma trivialSkewPrimitive_mem
  {k : Type u}
  {C : Type u}
  [Field k]
  [AddCommGroup C]
  [Module k C]
  [Coalgebra k C]
  {g h : C}
-- given
  (hg : IsGrouplike (R := k) g)
  (hh : IsGrouplike (R := k) h) :
-- imply
  IsSkewPrimitive (R := k) g h (h - g) := by
-- proof
  unfold IsSkewPrimitive
  rw [map_sub, hh.1, hg.1]
  simp [TensorProduct.sub_tmul, TensorProduct.tmul_sub]

/--
[trivialSkewPrimitive_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean)
-/
@[path]
lemma trivialSkewPrimitive_le
  {k : Type u}
  {C : Type u}
  [Field k]
  [AddCommGroup C]
  [Module k C]
  [Coalgebra k C]
  {g h : C}
-- given
  (hg : IsGrouplike (R := k) g)
  (hh : IsGrouplike (R := k) h) :
-- imply
  trivialSkewPrimitiveSubspace (k := k) g h ≤ skewPrimitiveSpace (R := k) g h := by
-- proof
  apply Submodule.span_le.mpr
  intro x hx
  simp at hx
  rw [hx]
  exact trivialSkewPrimitive_mem hg hh

/--
[coassoc_forces_skew_primitive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean)
-/
@[path]
lemma coassoc_forces_skew_primitive
  {k : Type u}
  {C : Type u}
  [Field k]
  [AddCommGroup C]
  [Module k C]
  [Coalgebra k C]
  {g h : C}
  {x : C}
-- given
  (_hg : IsGrouplike (R := k) g)
  (_hh : IsGrouplike (R := k) h)
  (hcoassoc : Coalgebra.comul (R := k) x = x ⊗ₜ[k] g + h ⊗ₜ[k] x) :
-- imply
  IsSkewPrimitive (R := k) g h x :=
-- proof
  hcoassoc

/--
[basis_change_shifts_by_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean)
-/
@[path]
lemma basis_change_shifts_by_trivial
  {k : Type u}
  {C : Type u}
  [Field k]
  [AddCommGroup C]
  [Module k C]
  [Coalgebra k C]
  {g h : C}
  {x : C}
  {c : k}
-- given
  (hg : IsGrouplike (R := k) g)
  (hh : IsGrouplike (R := k) h)
  (hx : IsSkewPrimitive (R := k) g h x) :
-- imply
  IsSkewPrimitive (R := k) g h (x + c • (h - g)) := by
-- proof
  unfold IsSkewPrimitive at *
  rw [map_add, LinearMap.map_smul, map_sub, hx, hh.1, hg.1]
  simp only [smul_sub, TensorProduct.tmul_sub, TensorProduct.sub_tmul,
    TensorProduct.tmul_add, TensorProduct.add_tmul,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  module
section Proposition_1_27_1_proof
variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/--
[Proposition_1_27_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean)
-/
@[path]
lemma Proposition_1_27_1
  {k : Type u}
  [Field k]
  {C : Type u}
  [AddCommGroup C]
  [Module k C]
  [Coalgebra k C]
-- given
  (g h : C)
  (_hg : IsGrouplike (R := k) g)
  (_hh : IsGrouplike (R := k) h) :
-- imply
  Nonempty ((skewPrimitiveSpace (R := k) g h ⧸ Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype (trivialSkewPrimitiveSubspace (k := k) g h)) ≃ₗ[k] ComoduleExt1 (k := k) g h) :=
-- proof
  ⟨(Equiv.linearEquiv k ext1EquivSkewQuot).symm⟩
namespace TensorCategories
/-- If a finite `k`-linear category has a unique simple object (up to iso) and `Ext¹(𝟙, 𝟙) = 0`,
then it is equivalent to the category of finite-dimensional `k`-vector spaces. -/
end TensorCategories

/--
[trivialSkewPrimitive_zero_when_equal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean)
-/
@[path]
lemma trivialSkewPrimitive_zero_when_equal
  {k : Type u}
  {C : Type u}
  [Field k]
  [AddCommGroup C]
  [Module k C]
  {g : C} :
-- imply
  trivialSkewPrimitiveSubspace (k := k) g g = ⊥ := by
-- proof
  unfold trivialSkewPrimitiveSubspace
  simp [sub_self]
section Corollary_1_27_6_proof
variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/--
[comoduleExtension_equiv_implies_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean)
-/
@[path]
lemma comoduleExtension_equiv_implies_eq
  {k : Type u}
  {C : Type u}
  [Field k]
  [AddCommGroup C]
  [Module k C]
  [Coalgebra k C]
  {g : C}
-- given
  (E₁ E₂ : ComoduleExtension (k := k) g g)
  (h : ComoduleExtension.Equiv E₁ E₂) :
-- imply
  E₁.x = E₂.x := by
-- proof
  unfold ComoduleExtension.Equiv at h
  rw [trivialSkewPrimitive_zero_when_equal] at h
  rw [Submodule.mem_bot] at h
  exact sub_eq_zero.mp h

/--
[skewPrimitiveSpace_eq_bot_of_ext1_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean)
-/
@[path]
lemma skewPrimitiveSpace_eq_bot_of_ext1_subsingleton
  {k : Type u}
  {C : Type u}
  [Field k]
  [AddCommGroup C]
  [Module k C]
  [Coalgebra k C]
  {g : C}
-- given
  (hsub : Subsingleton (ComoduleExt1 (k := k) g g)) :
-- imply
  skewPrimitiveSpace (R := k) g g = ⊥ := by
-- proof
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h0 : (0 : C) ∈ skewPrimitiveSpace (R := k) g g :=
    (skewPrimitiveSpace (R := k) g g).zero_mem
  let E₁ : ComoduleExtension (k := k) g g := ⟨x, hx⟩
  let E₀ : ComoduleExtension (k := k) g g := ⟨0, h0⟩
  have hq : Quotient.mk (ComoduleExtension.setoid (k := k) g g) E₁ =
    Quotient.mk (ComoduleExtension.setoid (k := k) g g) E₀ :=
    hsub.elim _ _
  exact comoduleExtension_equiv_implies_eq E₁ E₀ (Quotient.exact hq)
end Corollary_1_27_6_proof

/--
[primitiveElements_eq_skewPrimitiveSpace_one_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean)
-/
@[path]
lemma primitiveElements_eq_skewPrimitiveSpace_one_one
  {k : Type u}
  [Field k]
  {H : Type u}
  [Ring H]
  [Bialgebra k H] :
-- imply
  HopfAlgebra.primitiveElements (R := k) (H := H) = skewPrimitiveSpace (R := k) (1 : H) (1 : H) := by
-- proof
  ext x
  constructor <;> intro h <;> exact h

/--
[primitive_eq_skewPrimitive_one_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean)
-/
@[path]
lemma primitive_eq_skewPrimitive_one_one
  {k : Type u}
  {C : Type u}
  [Field k]
  [AddCommGroup C]
  [Module k C]
  [Coalgebra k C]
  {H : Type u}
  [Ring H]
  [Bialgebra k H]
  {x : H} :
-- imply
  HopfAlgebra.IsPrimitive (R := k) x ↔ IsSkewPrimitive (R := k) (1 : H) (1 : H) x := by
-- proof
  unfold HopfAlgebra.IsPrimitive IsSkewPrimitive
  constructor <;> intro h <;> exact h
end

/--
[ComoduleExtension.Equiv.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean)
-/
@[path]
private lemma refl_eq
  {k : Type u}
  {C : Type u}
  [Field k]
  [AddCommGroup C]
  [Module k C]
  [Coalgebra k C]
  {g h : C}
-- given
  (E : ComoduleExtension (k := k) g h) :
-- imply
  ComoduleExtension.Equiv E E := by
-- proof
  apply ComoduleExtension.Equiv.refl E

/--
[ComoduleExtension.Equiv.symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean)
-/
@[path]
private lemma symm_eq
  {k : Type u}
  {C : Type u}
  [Field k]
  [AddCommGroup C]
  [Module k C]
  [Coalgebra k C]
  {g h : C}
  {E₁ E₂ : ComoduleExtension (k := k) g h}
-- given
  (h_eq : ComoduleExtension.Equiv E₁ E₂) :
-- imply
  ComoduleExtension.Equiv E₂ E₁ := by
-- proof
  apply ComoduleExtension.Equiv.symm h_eq

/--
[ComoduleExtension.Equiv.trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean)
-/
@[path]
private lemma trans_eq
  {k : Type u}
  {C : Type u}
  [Field k]
  [AddCommGroup C]
  [Module k C]
  [Coalgebra k C]
  {g h : C}
  {E₁ E₂ E₃ : ComoduleExtension (k := k) g h}
-- given
  (h₁₂ : ComoduleExtension.Equiv E₁ E₂)
  (h₂₃ : ComoduleExtension.Equiv E₂ E₃) :
-- imply
  ComoduleExtension.Equiv E₁ E₃ := by
-- proof
  apply ComoduleExtension.Equiv.trans h₁₂ h₂₃


-- created on 2026-10-23
