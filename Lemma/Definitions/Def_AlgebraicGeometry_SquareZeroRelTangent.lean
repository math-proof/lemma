import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_SquareZeroDeformation

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

section

variable {k : Type u} [Field k] {X : Scheme.{u}}

def TangentPoints.zero (x : X ⟶ Spec (CommRingCat.of k)) (pt : Spec (CommRingCat.of k) ⟶ X)
    (hpt : pt ≫ x = 𝟙 (Spec (CommRingCat.of k)))
    (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V] : TangentPoints x pt V :=
  ⟨SquareZero.toBase k V ≫ pt, by rw [Category.assoc, hpt, Category.comp_id],
    by rw [SquareZero.basePoint_toBase_assoc]⟩

@[simp] theorem TangentPoints.zero_coe (x : X ⟶ Spec (CommRingCat.of k)) (pt : Spec (CommRingCat.of k) ⟶ X)
    (hpt : pt ≫ x = 𝟙 (Spec (CommRingCat.of k)))
    (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V] :
    (TangentPoints.zero x pt hpt V).1 = SquareZero.toBase k V ≫ pt := rfl

variable (x : X ⟶ Spec (CommRingCat.of k)) (pt : Spec (CommRingCat.of k) ⟶ X)
  (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
  {Z₀ Z : Scheme.{u}} (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
  (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))

def SquareZero.zeroSection : Z₀ ⟶ Z :=
  hZ.lift (𝟙 Z₀) (f₀ ≫ SquareZero.basePoint k V)
    (by rw [Category.id_comp, Category.assoc, SquareZero.basePoint_toBase, Category.comp_id])

@[reassoc (attr := simp)]
theorem SquareZero.zeroSection_fst : SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ q₁ = 𝟙 Z₀ :=
  hZ.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem SquareZero.zeroSection_snd :
    SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ q₂ = f₀ ≫ SquareZero.basePoint k V :=
  hZ.lift_snd _ _ _

def RelTangentPoints : Type u :=
  { w : Z ⟶ X // w ≫ x = q₂ ≫ SquareZero.toBase k V ∧
      SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w = f₀ ≫ pt }

namespace RelTangentPoints

variable {x pt V f₀ q₁ q₂ hZ}

@[ext] theorem ext {w w' : RelTangentPoints x pt V f₀ q₁ q₂ hZ} (h : w.1 = w'.1) : w = w' := Subtype.ext h

theorem comp_base (w : RelTangentPoints x pt V f₀ q₁ q₂ hZ) : w.1 ≫ x = q₂ ≫ SquareZero.toBase k V := w.2.1

theorem zeroSection_comp (w : RelTangentPoints x pt V f₀ q₁ q₂ hZ) :
    SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w.1 = f₀ ≫ pt := w.2.2

variable (x pt V f₀ q₁ q₂ hZ) in

def const (v : TangentPoints x pt V) : RelTangentPoints x pt V f₀ q₁ q₂ hZ :=
  ⟨q₂ ≫ v.1, by rw [Category.assoc, v.2.1],
    by rw [SquareZero.zeroSection_snd_assoc, v.2.2]⟩

@[simp] theorem const_coe (v : TangentPoints x pt V) : (const x pt V f₀ q₁ q₂ hZ v).1 = q₂ ≫ v.1 := rfl

end RelTangentPoints

end

end AlgebraicGeometry

end
