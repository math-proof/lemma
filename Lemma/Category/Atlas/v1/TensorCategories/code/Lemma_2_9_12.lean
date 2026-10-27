import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.Lemma_2_9_12
open CategoryTheory
open Category MonoidalCategory MonObj


namespace CategoryTheory

/--
[lemma_2_9_12](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_2_9_12.lean)
-/
@[path]
lemma lemma_2_9_12
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {A : C}
  [MonObj A]
  {A}
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {A : C}
  [MonObj A]
  {X : C}
  {M : RightMod' A} :
-- imply
  (∃ (fwd : RightMod'.Hom ⟨X ⊗ A, RightMod'.tensorModObj X (RightMod'.regular A)⟩ M → (X ⟶ M.X)) (bwd : (X ⟶ M.X) → RightMod'.Hom ⟨X ⊗ A, RightMod'.tensorModObj X (RightMod'.regular A)⟩ M), (∀ f, bwd (fwd f) = f) ∧ (∀ g, fwd (bwd g) = g)) := by
-- proof
  let e := RightMod'.Lemma_2_9_12 X M
  exact ⟨e.toFun, e.invFun, e.left_inv, e.right_inv⟩

end CategoryTheory


-- created on 2026-10-23
