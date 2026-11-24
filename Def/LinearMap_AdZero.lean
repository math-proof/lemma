module
public import Mathlib
public import Def.GaloisRep_Residual
public import Notation.GaloisRep_AdZero
set_option autoImplicit false


public section

namespace ResidualGaloisRep

variable {k : Type} [Field k]

open scoped GaloisRep_AdZero

noncomputable def adRep (ρbar : ResidualGaloisRep k) : Representation k Γℚ (Module.End k ρbar.V) where
  toFun σ := LinearMap.mulLeft k (ρbar.ρ σ) ∘ₗ LinearMap.mulRight k (ρbar.ρ σ⁻¹)
  map_one' := by
    ext f
    simp
  map_mul' σ τ := by
    ext f
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
      Module.End.mul_apply, mul_inv_rev, map_mul, mul_assoc]

noncomputable def adZeroRep (ρbar : ResidualGaloisRep k) :
    Representation k Γℚ (LinearMap.ker (LinearMap.trace k ρbar.V)) :=
  ρbar.adRep.subrepresentation _ ρbar.ker_trace_le_comap_adRep

noncomputable abbrev adZero (ρbar : ResidualGaloisRep k) : Rep k Γℚ :=
  Rep.of ρbar.adZeroRep

def adZeroFil (ρbar : ResidualGaloisRep k) (L : Submodule k ρbar.V) :
    Submodule k (LinearMap.ker (LinearMap.trace k ρbar.V)) where
  carrier := {f | (∀ v, (f : Module.End k ρbar.V) v ∈ L) ∧ ∀ v ∈ L, (f : Module.End k ρbar.V) v = 0}
  zero_mem' := ⟨fun _ => by simp, fun _ _ => by simp⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · simpa using L.add_mem (hf1 v) (hg1 v)
    · simp [hf2 v hv, hg2 v hv]
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · simpa using L.smul_mem c (hf1 v)
    · simp [hf2 v hv]

end ResidualGaloisRep
