module

public import Mathlib
public import Def.GaloisRep_Residual
public import Notation.GaloisRep_AdZero

public section

set_option autoImplicit false

namespace ResidualGaloisRep

variable {k : Type} [Field k]

open scoped GaloisRep_AdZero


@[simp]
public theorem adRep_apply (ρbar : ResidualGaloisRep k) (σ : Γℚ) (f : Module.End k ρbar.V) :
    ρbar.adRep σ f = ρbar.ρ σ * f * ρbar.ρ σ⁻¹ := rfl


public theorem trace_adRep_apply (ρbar : ResidualGaloisRep k) (σ : Γℚ) (f : Module.End k ρbar.V) :
    LinearMap.trace k ρbar.V (ρbar.adRep σ f) = LinearMap.trace k ρbar.V f := by
  rw [adRep_apply, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]


public theorem ker_trace_le_comap_adRep (ρbar : ResidualGaloisRep k) (σ : Γℚ) :
    LinearMap.ker (LinearMap.trace k ρbar.V) ≤ (LinearMap.ker (LinearMap.trace k ρbar.V)).comap (ρbar.adRep σ) := by
  intro f hf
  simp only [Submodule.mem_comap, LinearMap.mem_ker] at hf ⊢
  rw [trace_adRep_apply, hf]


@[simp]
public theorem adZeroRep_apply_coe (ρbar : ResidualGaloisRep k) (σ : Γℚ) (f : LinearMap.ker (LinearMap.trace k ρbar.V)) :
    ((ρbar.adZeroRep σ f : LinearMap.ker (LinearMap.trace k ρbar.V)) : Module.End k ρbar.V)
      = ρbar.ρ σ * (f : Module.End k ρbar.V) * ρbar.ρ σ⁻¹ :=
  rfl


public theorem adZero_ρ (ρbar : ResidualGaloisRep k) : ρbar.adZero.ρ = ρbar.adZeroRep := rfl


public theorem mem_adZeroFil_iff (ρbar : ResidualGaloisRep k) (L : Submodule k ρbar.V) (f : LinearMap.ker (LinearMap.trace k ρbar.V)) :
    f ∈ ρbar.adZeroFil L ↔ (∀ v, (f : Module.End k ρbar.V) v ∈ L) ∧ ∀ v ∈ L, (f : Module.End k ρbar.V) v = 0 :=
  Iff.rfl

end ResidualGaloisRep
