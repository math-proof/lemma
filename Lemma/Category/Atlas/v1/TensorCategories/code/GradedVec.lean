import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
open CategoryTheory CG


/--
[GroupCocycle3.ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean)
-/
@[path]
lemma GroupCocycle3.ext
  {G : Type u}
  [Monoid G]
  {A : Type v}
  [CommMonoid A]
  {ω₁ ω₂ : GroupCocycle3 G A}
-- given
  (h : ω₁.toFun = ω₂.toFun) :
-- imply
  ω₁ = ω₂ := by
-- proof
  cases ω₁; cases ω₂; congr

/--
[NormalizedGroupCocycle3.normalized_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean)
-/
@[path]
lemma NormalizedGroupCocycle3.normalized_right
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {ω : NormalizedGroupCocycle3 G A}
  {ω : NormalizedGroupCocycle3 G A}
-- given
  (g h : G) :
-- imply
  ω.toFun g h 1 = 1 := by
-- proof
  have hc := ω.cocycle_cond g h 1 1
  simp only [mul_one] at hc
  rw [ω.normalized (g * h) 1, ω.normalized h 1] at hc
  simp only [one_mul, mul_one] at hc
  have : ω.toFun g h 1 * ω.toFun g h 1 = ω.toFun g h 1 * 1 := by
    rw [mul_one]; exact hc.symm
  exact mul_left_cancel this

/--
[NormalizedGroupCocycle3.normalized_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean)
-/
@[path]
lemma NormalizedGroupCocycle3.normalized_left
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {ω : NormalizedGroupCocycle3 G A}
  {ω : NormalizedGroupCocycle3 G A}
-- given
  (g h : G) :
-- imply
  ω.toFun 1 g h = 1 := by
-- proof
  have hc := ω.cocycle_cond 1 1 g h
  simp only [one_mul] at hc
  rw [ω.normalized 1 (g * h), ω.normalized 1 g] at hc
  simp only [one_mul, mul_one] at hc
  have : ω.toFun 1 g h * ω.toFun 1 g h = ω.toFun 1 g h * 1 := by
    rw [mul_one]; exact hc.symm
  exact mul_left_cancel this

/--
[NormalizedGroupCocycle3.cocycle_inv_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean)
-/
@[path]
lemma NormalizedGroupCocycle3.cocycle_inv_cancel
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {ω : NormalizedGroupCocycle3 G A}
  {ω : NormalizedGroupCocycle3 G A}
  {g : G} :
-- imply
  ω.toFun g g⁻¹ g * ω.toFun g⁻¹ g g⁻¹ = 1 := by
-- proof
  have hc := ω.cocycle_cond g g⁻¹ g g⁻¹
  simp only [mul_inv_cancel, inv_mul_cancel] at hc
  rw [ω.normalized_left g g⁻¹, ω.normalized_right g g⁻¹, ω.normalized g g⁻¹] at hc
  simp only [mul_one] at hc
  exact hc.symm

/--
[Hom.ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean)
-/
@[path]
private lemma ext_eq_2
  {G : Type u}
  [Monoid G]
  {A : Type v}
  [CommGroup A]
  {ω : NormalizedGroupCocycle3 G A}
  {X Y : CG G A ω}
  {f f' : CG.Hom X Y}
-- given
  (hv : f.val = f'.val) :
-- imply
  f = f' := by
-- proof
  apply CG.Hom.ext hv

/--
[comp_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean)
-/
@[path]
private lemma comp_val_eq
  {G : Type u}
  [Monoid G]
  {A : Type v}
  [CommGroup A]
  {ω : NormalizedGroupCocycle3 G A}
  {X Y Z : CG G A ω}
  {f : X ⟶ Y}
  {g : Y ⟶ Z} :
-- imply
  (f ≫ g).val = f.val * g.val := by
-- proof
  apply CG.comp_val f g

/--
[id_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean)
-/
@[path]
private lemma id_val_eq
  {G : Type u}
  [Monoid G]
  {A : Type v}
  [CommGroup A]
  {ω : NormalizedGroupCocycle3 G A}
  {X : CG G A ω} :
-- imply
  (𝟙 X : X ⟶ X).val = 1 := by
-- proof
  apply CG.id_val X

/--
[twistedAssociator'_hom_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean)
-/
@[path]
private lemma twistedAssociator'_hom_val_eq
  {G : Type u}
  [Monoid G]
  {A : Type v}
  [CommGroup A]
  {ω : NormalizedGroupCocycle3 G A}
  {X Y Z : CG G A ω} :
-- imply
  (twistedAssociator' X Y Z).hom.val = ω.toFun X.val Y.val Z.val := by
-- proof
  apply CG.twistedAssociator'_hom_val X Y Z

/--
[twistedAssociator'_inv_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean)
-/
@[path]
private lemma twistedAssociator'_inv_val_eq
  {G : Type u}
  [Monoid G]
  {A : Type v}
  [CommGroup A]
  {ω : NormalizedGroupCocycle3 G A}
  {X Y Z : CG G A ω} :
-- imply
  (twistedAssociator' X Y Z).inv.val = (ω.toFun X.val Y.val Z.val)⁻¹ := by
-- proof
  apply CG.twistedAssociator'_inv_val X Y Z

/--
[leftUnitor'_hom_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean)
-/
@[path]
private lemma leftUnitor'_hom_val_eq
  {G : Type u}
  [Monoid G]
  {A : Type v}
  [CommGroup A]
  {ω : NormalizedGroupCocycle3 G A}
  {X : CG G A ω} :
-- imply
  (leftUnitor' X).hom.val = 1 := by
-- proof
  apply CG.leftUnitor'_hom_val X

/--
[rightUnitor'_hom_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean)
-/
@[path]
private lemma rightUnitor'_hom_val_eq
  {G : Type u}
  [Monoid G]
  {A : Type v}
  [CommGroup A]
  {ω : NormalizedGroupCocycle3 G A}
  {X : CG G A ω} :
-- imply
  (rightUnitor' X).hom.val = 1 := by
-- proof
  apply CG.rightUnitor'_hom_val X


-- created on 2026-10-23
