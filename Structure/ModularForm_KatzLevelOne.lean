import Mathlib
import Instance.ModularCurve_TateFormal

universe u

noncomputable section

open WeierstrassCurve

structure KatzModularForm (R : Type u) [CommRing R] (k : ℤ) : Type (u + 1) where

  toFun : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A), IsUnit W.Δ → A

  map_toFun : ∀ ⦃A B : Type u⦄ [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (hW' : IsUnit (W.map (f : A →+* B)).Δ), toFun (W.map (f : A →+* B)) hW' = f (toFun W hW)

  toFun_variableChange : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (C : VariableChange A)
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (hW' : IsUnit (C • W).Δ),
    toFun (C • W) hW' = ((C.u⁻¹ ^ k : Aˣ) : A) * toFun W hW

namespace KatzModularForm

variable {R : Type u} [CommRing R] {k l : ℤ}


variable (R)


variable {R}


end KatzModularForm

end
