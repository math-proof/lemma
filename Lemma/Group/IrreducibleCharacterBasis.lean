import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.IrreducibleCharacterBasis
open CategoryTheory
open scoped MonoidAlgebra
open MathlibExt.GroupTheory.ClassFunctionWanted
open FDRep
open MathlibExt.GroupTheory.IrreducibleCharacterBasisWanted


/--
[simple_of_isIrreducible](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/IrreducibleCharacterBasis.lean)
-/
@[path]
private lemma simple_of_isIrreducible_eq
  {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {G : Type v} [Group G]
  {ρ : Representation k G V} [ρ.IsIrreducible] :
-- imply
  Simple (FDRep.of ρ) := by
-- proof
  apply FDRep.simple_of_isIrreducible ρ

/--
[linearIndependent_character](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/IrreducibleCharacterBasis.lean)
-/
@[path]
private lemma linearIndependent_character_eq
  [Group G] [Finite G]
  {V : I → FDRep ℂ G} [∀ i, Simple (V i)]
-- given
  (hV : ∀ ⦃i j⦄, Nonempty (V i ≅ V j) → i = j) :
-- imply
  LinearIndependent ℂ fun i ↦ (V i).character := by
-- proof
  apply FDRep.linearIndependent_character V hV

/--
[eq_zero_of_isClassFunction_of_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/IrreducibleCharacterBasis.lean)
-/
@[path]
private lemma eq_zero_of_isClassFunction_of_orthogonal_eq
  [Group G] [Finite G]
  {f : G → ℂ}
-- given
  (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
  (horth : ∀ (W : FDRep ℂ G) [Simple W], (Nat.card G : ℂ)⁻¹ * ∑ᶠ g : G, f g * W.character g⁻¹ = 0) :
-- imply
  f = 0 := by
-- proof
  apply FDRep.eq_zero_of_isClassFunction_of_orthogonal f hf horth

/--
[linearIndependent_irrCharacters](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/IrreducibleCharacterBasis.lean)
-/
@[path]
private lemma linearIndependent_irrCharacters_eq
  [Group G] [Finite G] :
-- imply
  LinearIndependent ℂ (Subtype.val :
    {χ : G → ℂ // ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ} → (G → ℂ)) := by
-- proof
  apply MathlibExt.GroupTheory.IrreducibleCharacterBasisWanted.linearIndependent_irrCharacters G

/--
[mem_span_irrCharacters_of_isClassFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/IrreducibleCharacterBasis.lean)
-/
@[path]
private lemma mem_span_irrCharacters_of_isClassFunction_eq
  [Group G] [Finite G]
  {f : G → ℂ}
-- given
  (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
-- imply
  f ∈ Submodule.span ℂ
    {χ : G → ℂ | ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ} := by
-- proof
  apply MathlibExt.GroupTheory.IrreducibleCharacterBasisWanted.mem_span_irrCharacters_of_isClassFunction G f hf

/--
[card_irrCharacters_eq_card_conjClasses](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/IrreducibleCharacterBasis.lean)
-/
@[path]
private lemma card_irrCharacters_eq_card_conjClasses_eq
  [Group G] [Finite G] :
-- imply
  Nat.card {χ : G → ℂ // ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ} =
    Nat.card (ConjClasses G) := by
-- proof
  apply MathlibExt.GroupTheory.IrreducibleCharacterBasisWanted.card_irrCharacters_eq_card_conjClasses G


-- created on 2026-10-20
