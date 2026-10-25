import Mathlib
import Instance.AlgebraicGeometry_SquareZeroDeformation

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


variable (x : X ⟶ Spec (CommRingCat.of k)) (pt : Spec (CommRingCat.of k) ⟶ X)
  (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
  {Z₀ Z : Scheme.{u}} (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
  (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))

def SquareZero.zeroSection : Z₀ ⟶ Z :=
  hZ.lift (𝟙 Z₀) (f₀ ≫ SquareZero.basePoint k V)
    (by rw [Category.id_comp, Category.assoc, SquareZero.basePoint_toBase, Category.comp_id])


def RelTangentPoints : Type u :=
  { w : Z ⟶ X // w ≫ x = q₂ ≫ SquareZero.toBase k V ∧
      SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w = f₀ ≫ pt }

namespace RelTangentPoints

variable {x pt V f₀ q₁ q₂ hZ}


variable (x pt V f₀ q₁ q₂ hZ) in

def const (v : TangentPoints x pt V) : RelTangentPoints x pt V f₀ q₁ q₂ hZ :=
  ⟨q₂ ≫ v.1, by rw [Category.assoc, v.2.1],
    by rw [SquareZero.zeroSection_snd_assoc, v.2.2]⟩

end RelTangentPoints

end

end AlgebraicGeometry

end
