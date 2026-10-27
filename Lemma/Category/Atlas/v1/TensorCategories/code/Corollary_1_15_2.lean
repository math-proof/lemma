import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TensorCategories.code.Corollary_1_15_2
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits


/--
[Corollary_1_15_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_15_2.lean)
-/
@[path]
lemma Corollary_1_15_2
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [TensorCategories.MonoidalBiexact C]
  [IsArtinianRing (End (𝟙_ C))] :
-- imply
  ∃ (n : ℕ) (f : Fin n → C) (hbp : HasBiproduct f), (∀ i, Indecomposable (f i)) ∧ (∀ i j, i ≠ j → ¬Nonempty (f i ≅ f j)) ∧ Nonempty (𝟙_ C ≅ @biproduct _ _ _ _ f hbp) :=
-- proof
  TensorCategories.unit_indecomposable_decomposition TensorCategories.endUnit_isSemisimpleRing


-- created on 2026-10-23
