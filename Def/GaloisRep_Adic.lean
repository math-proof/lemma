import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Def.GaloisRep_Residual
import Def.GaloisRep_ResidualEquiv
import Structure.GaloisRep_Adic

open scoped TensorProduct


namespace GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]

def IsUnramifiedAt (ρ : GaloisRepAdic A) (q : ℕ) : Prop :=
  ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ = 1

noncomputable def det (ρ : GaloisRepAdic A) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ :=
  (LinearMap.det.comp ρ.ρ).toHomUnits

noncomputable def trace (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    A :=
  LinearMap.trace A ρ.V (ρ.ρ σ)

noncomputable def baseChangeAlong {B : Type} [CommRing B] [IsLocalRing B] (φ : A →+* B)
    (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) : GaloisRepAdic B :=
  letI : Algebra A B := φ.toAlgebra
  { V := B ⊗[A] ρ.V
    finrank_eq := by rw [Module.finrank_baseChange, ρ.finrank_eq]
    ρ := { toFun := fun σ => (ρ.ρ σ).baseChange B
           map_one' := by rw [map_one, LinearMap.baseChange_one]
           map_mul' := fun σ τ => by rw [map_mul, LinearMap.baseChange_mul] }
    isAdicContinuous := by
      intro n
      obtain ⟨L, hL, h1⟩ := ρ.isAdicContinuous n
      refine ⟨L, hL, fun σ hσ => ?_⟩
      have hmap : (IsLocalRing.maximalIdeal A ^ n).map φ ≤ IsLocalRing.maximalIdeal B ^ n := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun a ha =>
          Ideal.mem_comap.mpr (haveI := hφ; map_nonunit φ a ha)) n
      have hpure : ∀ (b : B) (v : ρ.V),
          (ρ.ρ σ).baseChange B (b ⊗ₜ[A] v) - b ⊗ₜ[A] v ∈
            (IsLocalRing.maximalIdeal B ^ n) • (⊤ : Submodule B (B ⊗[A] ρ.V)) := by
        intro b v
        rw [LinearMap.baseChange_tmul, ← TensorProduct.tmul_sub]
        refine Submodule.smul_induction_on (p := fun x => b ⊗ₜ[A] x ∈
          (IsLocalRing.maximalIdeal B ^ n) • (⊤ : Submodule B (B ⊗[A] ρ.V))) (h1 σ hσ v) ?_ ?_
        · intro a ha w _
          rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ← smul_eq_mul,
            ← TensorProduct.smul_tmul']
          exact Submodule.smul_mem_smul (hmap (Ideal.mem_map_of_mem φ ha)) Submodule.mem_top
        · intro x y hx hy
          rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ hx hy
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, sub_zero]; exact Submodule.zero_mem _
      | tmul b v => exact hpure b v
      | add x y hx hy =>
        rw [map_add, add_sub_add_comm]
        exact Submodule.add_mem _ hx hy }

noncomputable def residual (ρ : GaloisRepAdic A) :
    ResidualGaloisRep (IsLocalRing.ResidueField A) :=
  { V := IsLocalRing.ResidueField A ⊗[A] ρ.V
    finrank_eq := by rw [Module.finrank_baseChange, ρ.finrank_eq]
    ρ := { toFun := fun σ => (ρ.ρ σ).baseChange (IsLocalRing.ResidueField A)
           map_one' := by rw [map_one, LinearMap.baseChange_one]
           map_mul' := fun σ τ => by rw [map_mul, LinearMap.baseChange_mul] }
    factorsThroughFiniteLevel := by
      obtain ⟨L, hL, h1⟩ := ρ.isAdicContinuous 1
      refine ⟨L, hL, fun σ hσ => ?_⟩
      have hkill : ∀ x ∈ (IsLocalRing.maximalIdeal A ^ 1) • (⊤ : Submodule A ρ.V),
          ∀ c : IsLocalRing.ResidueField A, c ⊗ₜ[A] x = 0 := by
        intro x hx c
        refine Submodule.smul_induction_on
          (p := fun x => c ⊗ₜ[A] x = (0 : IsLocalRing.ResidueField A ⊗[A] ρ.V)) hx ?_ ?_
        · intro a ha w _
          rw [pow_one] at ha
          rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
            IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff a).mpr ha,
            zero_mul, TensorProduct.zero_tmul]
        · intro x y hx hy
          rw [TensorProduct.tmul_add, hx, hy, add_zero]
      refine LinearMap.ext fun w => ?_
      rw [MonoidHom.coe_mk, OneHom.coe_mk]
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul c v =>
        rw [LinearMap.baseChange_tmul, Module.End.one_apply, ← sub_eq_zero,
          ← TensorProduct.tmul_sub]
        exact hkill _ (h1 σ hσ v) c
      | add x y hx hy => rw [map_add, map_add, hx, hy] }


def IsEquiv (ρ₁ ρ₂ : GaloisRepAdic A) : Prop :=
  Nonempty (Equiv ρ₁ ρ₂)

namespace Equiv

def refl (ρ : GaloisRepAdic A) : Equiv ρ ρ :=
  { toLinearEquiv := LinearEquiv.refl A ρ.V
    map_apply := fun _ _ => rfl }

def symm {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂) : Equiv ρ₂ ρ₁ :=
  { toLinearEquiv := e.toLinearEquiv.symm
    map_apply := fun σ y => e.toLinearEquiv.injective (by
      rw [LinearEquiv.apply_symm_apply, e.map_apply, LinearEquiv.apply_symm_apply]) }

def trans {ρ₁ ρ₂ ρ₃ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂) (e' : Equiv ρ₂ ρ₃) : Equiv ρ₁ ρ₃ :=
  { toLinearEquiv := e.toLinearEquiv.trans e'.toLinearEquiv
    map_apply := fun σ x => by
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e.map_apply, e'.map_apply] }

noncomputable def baseChangeAlong {B : Type} [CommRing B] [IsLocalRing B] (φ : A →+* B)
    (hφ : IsLocalHom φ) {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂) :
    Equiv (ρ₁.baseChangeAlong φ hφ) (ρ₂.baseChangeAlong φ hφ) :=
  letI : Algebra A B := φ.toAlgebra
  { toLinearEquiv := e.toLinearEquiv.baseChange A B ρ₁.V ρ₂.V
    map_apply := fun σ x => by
      show e.toLinearEquiv.baseChange A B ρ₁.V ρ₂.V ((ρ₁.ρ σ).baseChange B x) =
        (ρ₂.ρ σ).baseChange B (e.toLinearEquiv.baseChange A B ρ₁.V ρ₂.V x)
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b v =>
        rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
          LinearMap.baseChange_tmul, e.map_apply]
      | add x y hx hy => simp only [map_add, hx, hy] }

end Equiv

end GaloisRepAdic

namespace GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]

noncomputable def Equiv.residual {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂) :
    ResidualGaloisRep.Equiv ρ₁.residual ρ₂.residual :=
  { toLinearEquiv :=
      e.toLinearEquiv.baseChange A (IsLocalRing.ResidueField A) ρ₁.V ρ₂.V
    map_apply := fun σ x => by
      show e.toLinearEquiv.baseChange A (IsLocalRing.ResidueField A) ρ₁.V ρ₂.V
          ((ρ₁.ρ σ).baseChange (IsLocalRing.ResidueField A) x) =
        (ρ₂.ρ σ).baseChange (IsLocalRing.ResidueField A)
          (e.toLinearEquiv.baseChange A (IsLocalRing.ResidueField A) ρ₁.V ρ₂.V x)
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b v =>
        rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
          LinearMap.baseChange_tmul, e.map_apply]
      | add x y hx hy => simp only [map_add, hx, hy] }

def toResidualGaloisRep {k : Type} [Field k] (ρ : GaloisRepAdic k) : ResidualGaloisRep k :=
  { V := ρ.V
    finrank_eq := ρ.finrank_eq
    ρ := ρ.ρ
    factorsThroughFiniteLevel := by
      obtain ⟨L, hL, h1⟩ := ρ.isAdicContinuous 1
      refine ⟨L, hL, fun σ hσ => LinearMap.ext fun v => ?_⟩
      have hbot : IsLocalRing.maximalIdeal k = ⊥ :=
        (Ideal.eq_bot_or_top _).resolve_right (Ideal.IsMaximal.ne_top inferInstance)
      have h := h1 σ hσ v
      rw [hbot, pow_one, Submodule.bot_smul, Submodule.mem_bot, sub_eq_zero] at h
      exact h }

def ofResidualGaloisRep {k : Type} [Field k] (ρ : ResidualGaloisRep k) : GaloisRepAdic k :=
  { V := ρ.V
    finrank_eq := ρ.finrank_eq
    ρ := ρ.ρ
    isAdicContinuous := by
      intro n
      obtain ⟨L, hL, h1⟩ := ρ.factorsThroughFiniteLevel
      refine ⟨L, hL, fun σ hσ v => ?_⟩
      rw [h1 σ hσ, Module.End.one_apply, sub_self]
      exact Submodule.zero_mem _ }

end GaloisRepAdic
