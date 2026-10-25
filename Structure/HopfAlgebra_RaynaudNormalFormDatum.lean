import Mathlib
import Structure.HopfAlgebra_FVectStructure
import Class.HopfAlgebra_HopfTower
import Instance.Compat_Mathlib430

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace HopfAlgebra

section Cotangent

variable (R : Type*) [CommRing R] (B : Type*) [CommRing B] [HopfAlgebra R B]


end Cotangent

namespace FVect

variable (R' : Type*) [CommRing R'] (p r : ℕ) [NeZero r] (F : Type*) [Field F] [Fintype F]
  (B : Type*) [CommRing B] [HopfAlgebra R' B] (fv : FVectStructure F R' B) (χ : Fˣ →* R'ˣ)

structure NormalFormDatum where
  X : Fin r → B
  δ : Fin r → R'
  act_X : ∀ (i : Fin r) (l : Fˣ), fv.act l (X i) = (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • X i
  pow_X : ∀ i : Fin r, X i ^ p = δ i • X (i + 1)
  δ_dvd : ∀ i : Fin r, δ i ∣ (p : R')
  counit_X : ∀ i : Fin r, Coalgebra.counit (R := R') (X i) = 0
  adjoin_X : Algebra.adjoin R' (Set.range X) = ⊤

namespace NormalFormDatum

variable {R' p r F B fv χ}
variable (D : NormalFormDatum R' p r F B fv χ)


end NormalFormDatum

variable (R : Type*) [CommRing R] [Algebra R R'] (Γ : Type*) [Group Γ] [MulSemiringAction Γ R']

structure DescentDatum where
  g : Γ →* (B ≃+* B)
  semilinear : ∀ (σ : Γ) (c : R') (b : B), g σ (c • b) = (σ • c) • g σ b
  fixes_base : ∀ (σ : Γ) (c : R), σ • (algebraMap R R' c) = algebraMap R R' c
  counit_g : ∀ (σ : Γ) (b : B), Coalgebra.counit (R := R') (g σ b) = σ • Coalgebra.counit (R := R') b
  act_g : ∀ (σ : Γ) (l : F) (b : B), fv.act l (g σ b) = g σ (fv.act l b)

namespace DescentDatum

variable {R' p r F B fv χ R Γ}


structure CotAction (Dd : DescentDatum R' F B fv R Γ) where

  cotAct : Γ →* AddAut (Cot R' B)
  cotAct_spec : ∀ (σ : Γ) (x : augIdeal R' B),
    cotAct σ ((augIdeal R' B).toCotangent x) =
      (augIdeal R' B).toCotangent ⟨Dd.g σ x, by
        have hx := x.2
        rw [HopfAlgebra.mem_augIdeal] at hx ⊢
        rw [Dd.counit_g, hx, smul_zero]⟩

end DescentDatum

end FVect

end HopfAlgebra

end
