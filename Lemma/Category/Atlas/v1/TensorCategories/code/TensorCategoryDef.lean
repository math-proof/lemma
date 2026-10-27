import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
open CategoryTheory MonoidalCategory Limits
open TensorCategories


/--
[schur_hom_eq_zero_of_not_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorCategoryDef.lean)
-/
@[path]
lemma schur_hom_eq_zero_of_not_iso
  [Field k]
  [IsAlgClosed k]
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Linear k C]
  [Abelian C]
  [LocallyFiniteCategory k C]
  {X Y : C}
  [Simple X]
  [Simple Y]
-- given
  (h : (X ≅ Y) → False) :
-- imply
  ∀ (f : X ⟶ Y), f = 0 := by
-- proof
  intro f
  have := subsingleton_of_forall_eq (0 : X ⟶ Y) fun g => by
    have p := not_congr (isIso_iff_nonzero g)
    simp only [Classical.not_not, Ne] at p
    exact p.mp fun _ => h (asIso g)
  exact Subsingleton.elim f 0


-- created on 2026-10-23
