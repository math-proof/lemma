import Mathlib
import Initialize.Tactic.Attr.Basic
open Set Topology


/--
[irreducibleSpace_def'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IrreducibleSpaceDef.lean)
-/
@[path]
lemma irreducibleSpace_def'
  [TopologicalSpace X] :
-- imply
  IrreducibleSpace X ↔ IsIrreducible (⊤ : Set X) :=
-- proof
  irreducibleSpace_def X
section Equivalences
variable [IrreducibleSpace X]

/--
[IrreducibleSpace.nonempty_inter_of_open](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IrreducibleSpaceDef.lean)
-/
@[path]
lemma IrreducibleSpace.nonempty_inter_of_open
  [TopologicalSpace X]
  [IrreducibleSpace X]
  {U V : Set X}
-- given
  (hU : IsOpen U)
  (hV : IsOpen V)
  (hU' : U.Nonempty)
  (hV' : V.Nonempty) :
-- imply
  (U ∩ V).Nonempty :=
-- proof
  nonempty_preirreducible_inter hU hV hU' hV'

/--
[IrreducibleSpace.eq_univ_of_isClosed_union](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IrreducibleSpaceDef.lean)
-/
@[path]
lemma IrreducibleSpace.eq_univ_of_isClosed_union
  [TopologicalSpace X]
  [IrreducibleSpace X]
  {Z₁ Z₂ : Set X}
-- given
  (hZ₁ : IsClosed Z₁)
  (hZ₂ : IsClosed Z₂)
  (h : Z₁ ∪ Z₂ = univ) :
-- imply
  Z₁ = univ ∨ Z₂ = univ := by
-- proof
  have hirr := PreirreducibleSpace.isPreirreducible_univ (X := X)
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hirr
  have hsub : (univ : Set X) ⊆ Z₁ ∪ Z₂ := h ▸ le_refl _
  cases hirr Z₁ Z₂ hZ₁ hZ₂ hsub with
  | inl h => exact Or.inl (eq_univ_of_univ_subset h)
  | inr h => exact Or.inr (eq_univ_of_univ_subset h)

/--
[IrreducibleSpace.dense_of_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IrreducibleSpaceDef.lean)
-/
@[path]
lemma IrreducibleSpace.dense_of_isOpen
  [TopologicalSpace X]
  [IrreducibleSpace X]
  {U : Set X}
-- given
  (hU : IsOpen U)
  (hne : U.Nonempty) :
-- imply
  Dense U :=
-- proof
  hU.dense hne
end Equivalences

/--
[irreducibleSpace_of_nonempty_inter](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IrreducibleSpaceDef.lean)
-/
@[path]
lemma irreducibleSpace_of_nonempty_inter
  [TopologicalSpace X]
  [Nonempty X]
-- given
  (h : ∀ ⦃U V : Set X⦄, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty → (U ∩ V).Nonempty) :
-- imply
  IrreducibleSpace X where toPreirreducibleSpace :=
-- proof
  PreirreducibleSpace.of_forall_nonempty_inter h
    toNonempty := ‹_›


-- created on 2026-10-23
