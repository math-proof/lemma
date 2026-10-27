import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial IntermediateField Module


namespace FiniteFields

/--
[finite_field_units_cyclic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/FiniteFields.lean)
-/
@[path]
lemma finite_field_units_cyclic
  {F : Type*}
  [Field F]
  {G : Subgroup Fˣ}
  [Finite ↥G] :
-- imply
  IsCyclic ↥G :=
-- proof
  inferInstance

end FiniteFields

namespace FiniteFields

/--
[finite_field_existence_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/FiniteFields.lean)
-/
@[path]
lemma finite_field_existence_uniqueness
  {p : ℕ}
  [hp : Fact p.Prime]
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  Nat.card (GaloisField p n) = p ^ n ∧ ∀ (K : Type*) [Field K] [Algebra (ZMod p) K], Nat.card K = p ^ n → Nonempty (K ≃ₐ[ZMod p] GaloisField p n) := by
-- proof
  constructor
  · exact GaloisField.card p n hn
  · intro K _ _ hK
    exact ⟨GaloisField.algEquivGaloisField p n hK⟩
open Polynomial IntermediateField Module

end FiniteFields

namespace FiniteFields

/--
[finite_field_simple_extension_and_irreducibles](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/FiniteFields.lean)
-/
@[path]
lemma finite_field_simple_extension_and_irreducibles
  {p : ℕ}
  [hp : Fact p.Prime]
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (∃ α : GaloisField p n, (ZMod p)⟮α⟯ = ⊤) ∧ (∃ f : Polynomial (ZMod p), Irreducible f ∧ f.natDegree = n) := by
-- proof
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  constructor
  ·
    exact Field.exists_primitive_element_of_finite_top (ZMod p) (GaloisField p n)
  ·
    obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top (ZMod p) (GaloisField p n)
    refine ⟨minpoly (ZMod p) α, minpoly.irreducible (IsIntegral.of_finite _ _), ?_⟩
    have h1 := (Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p) α).mp hα
    rw [h1, GaloisField.finrank p hne]

end FiniteFields


-- created on 2026-10-23
