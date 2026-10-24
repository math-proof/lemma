import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_1_27_1
open EGNO.Prop1271 in EGNO


/--
[EGNO.Proposition_1_27_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_27_1.lean)
-/
@[path]
lemma EGNO.Proposition_1_27_1
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

/--
[ComoduleExtension.Equiv.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_27_1.lean)
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
  apply EGNO.Prop1271.ComoduleExtension.Equiv.refl E

/--
[ComoduleExtension.Equiv.symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_27_1.lean)
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
  apply EGNO.Prop1271.ComoduleExtension.Equiv.symm h_eq

/--
[ComoduleExtension.Equiv.trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_27_1.lean)
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
  apply EGNO.Prop1271.ComoduleExtension.Equiv.trans h₁₂ h₂₃


-- created on 2026-10-23
