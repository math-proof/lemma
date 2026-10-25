import Mathlib
import Lemma.HopfAlgebra.FVectStructure
import Class.HopfAlgebra_HopfTower
import Lemma.Compat.Mathlib430
import Structure.HopfAlgebra_RaynaudNormalFormDatum
import Abbrev.HopfAlgebra_RaynaudNormalFormDatum

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace HopfAlgebra

section Cotangent

variable (R : Type*) [CommRing R] (B : Type*) [CommRing B] [HopfAlgebra R B]

def CotSpecial [IsLocalRing R] : Type _ :=
  letI : Algebra B (IsLocalRing.ResidueField R) :=
    ((IsLocalRing.residue R).comp (Bialgebra.counitAlgHom R B).toRingHom).toAlgebra
  (IsLocalRing.ResidueField R) ⊗[B] (augIdeal R B).Cotangent

end Cotangent

namespace FVect

variable (R' : Type*) [CommRing R'] (p r : ℕ) [NeZero r] (F : Type*) [Field F] [Fintype F]
  (B : Type*) [CommRing B] [HopfAlgebra R' B] (fv : FVectStructure F R' B) (χ : Fˣ →* R'ˣ)


namespace NormalFormDatum

variable {R' p r F B fv χ}
variable (D : NormalFormDatum R' p r F B fv χ)

def digit [IsDomain R'] [IsDiscreteValuationRing R'] (i : Fin r) : ℕ :=
  (IsDiscreteValuationRing.addVal R' (D.δ i)).toNat

def _root_.HopfAlgebra.FVect.ramification (R' : Type*) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] (p : ℕ) : ℕ :=
  (IsDiscreteValuationRing.addVal R' (p : R')).toNat

def IsEtale [IsDomain R'] [IsDiscreteValuationRing R'] : Prop := ∀ i : Fin r, D.digit i = 0

def IsMultiplicative [IsDomain R'] [IsDiscreteValuationRing R'] : Prop := ∀ i : Fin r, D.digit i = ramification R' p

def IsLocalLocal [IsDomain R'] [IsDiscreteValuationRing R'] : Prop :=
  (∃ i : Fin r, 0 < D.digit i) ∧ (∃ i : Fin r, D.digit i < ramification R' p)

def tameExponent [IsDomain R'] [IsDiscreteValuationRing R'] : ℕ := ∑ i : Fin r, D.digit i * p ^ (i : ℕ)

end NormalFormDatum

variable (R : Type*) [CommRing R] [Algebra R R'] (Γ : Type*) [Group Γ] [MulSemiringAction Γ R']


namespace DescentDatum

variable {R' p r F B fv χ R Γ}

def gTensor (Dd : DescentDatum R' F B fv R Γ) (σ : Γ) : B ⊗[R'] B →+ B ⊗[R'] B :=
  TensorProduct.liftAddHom
    { toFun := fun b₁ =>
        { toFun := fun b₂ => Dd.g σ b₁ ⊗ₜ[R'] Dd.g σ b₂
          map_zero' := by simp only [map_zero, TensorProduct.tmul_zero]
          map_add' := fun x y => by simp only [map_add, TensorProduct.tmul_add] }
      map_zero' := by
        ext b₂
        simp only [map_zero, TensorProduct.zero_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply]
      map_add' := fun x y => by
        ext b₂
        simp only [map_add, TensorProduct.add_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply] }
    (fun c b₁ b₂ => by
      show Dd.g σ (c • b₁) ⊗ₜ[R'] Dd.g σ b₂ = Dd.g σ b₁ ⊗ₜ[R'] Dd.g σ (c • b₂)
      rw [Dd.semilinear, Dd.semilinear, TensorProduct.smul_tmul])

theorem gTensor_tmul (Dd : DescentDatum R' F B fv R Γ) (σ : Γ) (b₁ b₂ : B) :
    Dd.gTensor σ (b₁ ⊗ₜ[R'] b₂) = Dd.g σ b₁ ⊗ₜ[R'] Dd.g σ b₂ := rfl

def IsComulCompatible (Dd : DescentDatum R' F B fv R Γ) : Prop :=
  ∀ (σ : Γ) (b : B), Coalgebra.comul (R := R') (Dd.g σ b) = Dd.gTensor σ (Coalgebra.comul (R := R') b)


end DescentDatum

end FVect

end HopfAlgebra

end
