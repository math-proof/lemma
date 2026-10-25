import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.Proposition_1_36_4.Part4
open CategoryTheory
open scoped TensorProduct
open TensorCategories


/--
[Prop1364.GaugeEquiv.equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean)
-/
@[path]
lemma Prop1364.GaugeEquiv.equivalence
  {R : Type u}
  [CommSemiring R]
  {H : Type u}
  [Semiring H]
  [Bialgebra R H] :
-- imply
  Equivalence (Prop1364.GaugeEquiv (R := R) (H := H)) where refl :=
-- proof
  Prop1364.GaugeEquiv.refl
    symm := Prop1364.GaugeEquiv.symm
    trans := Prop1364.GaugeEquiv.trans
section Prop1364Classes
variable (R : Type u) [CommSemiring R]
variable (H : Type u) [Semiring H] [Bialgebra R H]

/--
[isMonoidal_inv_of_isMonoidal_hom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean)
-/
@[path]
private lemma isMonoidal_inv_of_isMonoidal_hom_eq
  [Category C]
  [MonoidalCategory C]
  {lmF : F.LaxMonoidal}
  {lmG : G.LaxMonoidal}
  {α : F ≅ G}
-- given
  (hα : @NatTrans.IsMonoidal _ _ _ _ _ _ F G α.hom lmF lmG) :
-- imply
  @NatTrans.IsMonoidal _ _ _ _ _ _ G F α.inv lmG lmF := by
-- proof
  apply isMonoidal_inv_of_isMonoidal_hom α hα

/--
[isMonoidal_comp_of_isMonoidal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean)
-/
@[path]
private lemma isMonoidal_comp_of_isMonoidal_eq
  [Category C]
  [MonoidalCategory C]
  {lmF : F.LaxMonoidal}
  {lmG : G.LaxMonoidal}
  {lmH : H.LaxMonoidal}
  {α : F ⟶ G}
  {β : G ⟶ H}
-- given
  (hα : @NatTrans.IsMonoidal _ _ _ _ _ _ F G α lmF lmG)
  (hβ : @NatTrans.IsMonoidal _ _ _ _ _ _ G H β lmG lmH) :
-- imply
  @NatTrans.IsMonoidal _ _ _ _ _ _ F H (α ≫ β) lmF lmH := by
-- proof
  apply isMonoidal_comp_of_isMonoidal α β hα hβ

/--
[Prop1364.GaugeEquiv.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean)
-/
@[path]
private lemma refl_eq
  {R : Type u}
  [CommSemiring R]
  {H : Type u}
  [Semiring H]
  [Bialgebra R H]
  {J : (H ⊗[R] H)ˣ} :
-- imply
  Prop1364.GaugeEquiv J J := by
-- proof
  apply Prop1364.GaugeEquiv.refl J

/--
[Prop1364.GaugeEquiv.symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean)
-/
@[path]
private lemma symm_eq
  {R : Type u}
  [CommSemiring R]
  {H : Type u}
  [Semiring H]
  [Bialgebra R H]
  {J₁ J₂ : (H ⊗[R] H)ˣ}
-- given
  (h : Prop1364.GaugeEquiv J₁ J₂) :
-- imply
  Prop1364.GaugeEquiv J₂ J₁ := by
-- proof
  apply Prop1364.GaugeEquiv.symm h

/--
[Prop1364.GaugeEquiv.trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean)
-/
@[path]
private lemma trans_eq
  {R : Type u}
  [CommSemiring R]
  {H : Type u}
  [Semiring H]
  [Bialgebra R H]
  {J₁ J₂ J₃ : (H ⊗[R] H)ˣ}
-- given
  (h₁₂ : Prop1364.GaugeEquiv J₁ J₂)
  (h₂₃ : Prop1364.GaugeEquiv J₂ J₃) :
-- imply
  Prop1364.GaugeEquiv J₁ J₃ := by
-- proof
  apply Prop1364.GaugeEquiv.trans h₁₂ h₂₃

/--
[Prop1364.FiberFunctorMonoidalIsomorphic.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean)
-/
@[path]
private lemma refl_eq_2
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  {FF : FiberFunctor k C} :
-- imply
  Prop1364.FiberFunctorMonoidalIsomorphic FF FF := by
-- proof
  apply Prop1364.FiberFunctorMonoidalIsomorphic.refl FF

/--
[Prop1364.FiberFunctorMonoidalIsomorphic.symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean)
-/
@[path]
private lemma symm_eq_2
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  {FF₁ FF₂ : FiberFunctor k C}
-- given
  (h : Prop1364.FiberFunctorMonoidalIsomorphic FF₁ FF₂) :
-- imply
  Prop1364.FiberFunctorMonoidalIsomorphic FF₂ FF₁ := by
-- proof
  apply Prop1364.FiberFunctorMonoidalIsomorphic.symm h

/--
[Prop1364.FiberFunctorMonoidalIsomorphic.trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean)
-/
@[path]
private lemma trans_eq_2
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  {FF₁ FF₂ FF₃ : FiberFunctor k C}
-- given
  (h₁₂ : Prop1364.FiberFunctorMonoidalIsomorphic FF₁ FF₂)
  (h₂₃ : Prop1364.FiberFunctorMonoidalIsomorphic FF₂ FF₃) :
-- imply
  Prop1364.FiberFunctorMonoidalIsomorphic FF₁ FF₃ := by
-- proof
  apply Prop1364.FiberFunctorMonoidalIsomorphic.trans h₁₂ h₂₃

/--
[Prop1364.FiberFunctorMonoidalIsomorphic.equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean)
-/
@[path]
private lemma equivalence_eq_2
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C] :
-- imply
  Equivalence (Prop1364.FiberFunctorMonoidalIsomorphic (k := k) (C := C)) where refl := by
-- proof
  apply Prop1364.FiberFunctorMonoidalIsomorphic.equivalence


-- created on 2026-10-23
