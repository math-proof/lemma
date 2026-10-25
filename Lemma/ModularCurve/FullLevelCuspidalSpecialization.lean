import Lemma.ModularCurve.FullLevelJacobian
import Lemma.Matrix.TateProdRep.eq.TateRep
import Def.ModularCurve_FullLevelCuspidalSpecialization

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace ModularCurve.FullLevel

section Coord

variable (q : ℕ) (M' : ℕ) (lam : ℕ) [Fact lam.Prime]


@[simp] theorem ratCoord_tmul
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (ζ : Idx q) (a : ℚ_[lam]) (x : TateModule lam (Jac q M')) :
    ratCoord q M' lam Ψ ζ (a ⊗ₜ x) = a ⊗ₜ Ψ x ζ :=
  rfl

end Coord

section Specialization

variable (q : ℕ) (M' : ℕ) (lam : ℕ) [Fact lam.Prime] (k : Type) [Field k] [IsDomain (DrinfeldCurve.CoordRing q k)]


variable
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (eC : RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] RationalTateModule lam (Jac q M'))
    (Vinv : Submodule ℚ_[lam] (RationalTateModule lam (jacComp q M')))
    (eInv : RationalTateModule lam (jacComp q M') →ₗ[ℚ_[lam]] ↥Vinv)
    {n : ℕ} {Y : Fin n → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℚ_[lam] (Y i)]
    (red : ↥Vinv →ₗ[ℚ_[lam]] ((i : Fin n) → Y i))
    {T : Type} (c : T → Fin n)
    (Φ : (ζ : Idx q) → (t : T) →
      (Y (c t) →ₗ[ℚ_[lam]] RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))))

@[simp] theorem componentSpecialization_apply (v : RationalTateModule lam (Jac q M')) (p : Idx q × T) :
    componentSpecialization q M' lam k Ψ Vinv eInv red c Φ v p =
      (1 : ℚ_[lam]) ⊗ₜ Φ p.1 p.2 (red (eInv (ratCoord q M' lam Ψ p.1 v)) (c p.2)) :=
  rfl

theorem cuspidalSpecialization_apply' (v : RationalTateModule lam (Jac q M')) :
    cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ v =
      componentSpecialization q M' lam k Ψ Vinv eInv red c Φ (eC v) :=
  rfl

@[simp] theorem cuspidalSpecialization_apply (v : RationalTateModule lam (Jac q M')) (p : Idx q × T) :
    cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ v p =
      (1 : ℚ_[lam]) ⊗ₜ Φ p.1 p.2 (red (eInv (ratCoord q M' lam Ψ p.1 (eC v))) (c p.2)) :=
  rfl

theorem proj_comp_cuspidalSpecialization (p : Idx q × T) :
    LinearMap.proj p ∘ₗ cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ =
      TensorProduct.mk ℚ_[lam] ℚ_[lam]
          (RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))) 1 ∘ₗ
        Φ p.1 p.2 ∘ₗ LinearMap.proj (c p.2) ∘ₗ red ∘ₗ eInv ∘ₗ ratCoord q M' lam Ψ p.1 ∘ₗ eC :=
  rfl

theorem cuspidalSpecialization_apply_eq_of_apply_eq (v w : RationalTateModule lam (Jac q M'))
    (h : eC v = eC w) :
    cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ v =
      cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ w :=
  congrArg (componentSpecialization q M' lam k Ψ Vinv eInv red c Φ) h

theorem cuspidalSpecialization_apply_of_apply_eq_self (v : RationalTateModule lam (Jac q M'))
    (hv : eC v = v) :
    cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ v =
      componentSpecialization q M' lam k Ψ Vinv eInv red c Φ v :=
  congrArg (componentSpecialization q M' lam k Ψ Vinv eInv red c Φ) hv

theorem cuspidalSpecialization_apply_eq_zero_of_apply_eq_zero (v : RationalTateModule lam (Jac q M'))
    (hv : eC v = 0) : cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ v = 0 :=
  (congrArg (componentSpecialization q M' lam k Ψ Vinv eInv red c Φ) hv).trans
    (LinearMap.map_zero _)

theorem componentSpecialization_apply_eq_zero_iff (v : RationalTateModule lam (Jac q M')) :
    componentSpecialization q M' lam k Ψ Vinv eInv red c Φ v = 0 ↔
      ∀ (ζ : Idx q) (t : T), Φ ζ t (red (eInv (ratCoord q M' lam Ψ ζ v)) (c t)) = 0 := by
  have key : ∀ x : RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k)),
      TensorProduct.mk ℚ_[lam] ℚ_[lam] _ 1 x = 0 ↔ x = 0 := fun x =>
    (TensorProduct.lid ℚ_[lam] _).symm.map_eq_zero_iff
  constructor
  · intro h ζ t
    exact (key _).mp (congrFun h (ζ, t))
  · intro h
    funext p
    exact (key _).mpr (h p.1 p.2)

theorem cuspidalSpecialization_apply_eq_zero_iff (v : RationalTateModule lam (Jac q M')) :
    cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ v = 0 ↔
      ∀ (ζ : Idx q) (t : T), Φ ζ t (red (eInv (ratCoord q M' lam Ψ ζ (eC v))) (c t)) = 0 :=
  componentSpecialization_apply_eq_zero_iff q M' lam k Ψ Vinv eInv red c Φ (eC v)

end Specialization

end ModularCurve.FullLevel

end
