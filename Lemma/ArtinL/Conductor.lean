import Mathlib
import Lemma.ArtinL.EulerFactor
import Lemma.RingTheory.Valuation.LowerRamificationGroup
import Instance.ArtinL_Conductor
import Notation.ArtinL_Conductor

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups Pointwise

namespace ArtinL

variable {n : ℕ}

open scoped ArtinL_Conductor

def splittingField (ρ : Γℚ →* GL (Fin n) ℂ) : IntermediateField ℚ ℚbar :=
  IntermediateField.fixedField ρ.ker

theorem apply_mem_splittingField (ρ : Γℚ →* GL (Fin n) ℂ) (σ : Γℚ) {x : ℚbar}
    (hx : x ∈ splittingField ρ) : σ x ∈ splittingField ρ := by
  rintro ⟨τ, hτ⟩
  change τ (σ x) = σ x
  have hmem : σ⁻¹ * τ * σ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker] at hτ ⊢
    rw [map_mul, map_mul, hτ, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have h := hx ⟨σ⁻¹ * τ * σ, hmem⟩
  change (σ⁻¹ * τ * σ) x = x at h
  simpa [AlgEquiv.mul_apply] using congrArg σ h

@[simp] theorem coe_smul_splittingField (ρ : Γℚ →* GL (Fin n) ℂ) (σ : Γℚ)
    (x : splittingField ρ) : ((σ • x : splittingField ρ) : ℚbar) = σ (x : ℚbar) := rfl

def placeUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) :
    ValuationSubring (splittingField ρ) :=
  A.comap (algebraMap (splittingField ρ) ℚbar)

theorem mem_placeUnder_iff (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (x : splittingField ρ) : x ∈ placeUnder ρ A ↔ (x : ℚbar) ∈ A := Iff.rfl

theorem smul_mem_placeUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (σ : A.decompositionSubgroup ℚ) {x : splittingField ρ} (hx : x ∈ placeUnder ρ A) :
    (σ : Γℚ) • x ∈ placeUnder ρ A := by
  rw [mem_placeUnder_iff] at hx ⊢
  have h : (σ : Γℚ) • (x : ℚbar) ∈ (σ : Γℚ) • (A : ValuationSubring ℚbar) :=
    Set.smul_mem_smul_set hx
  rw [σ.2] at h
  exact h

@[simp] theorem coe_coe_smul_placeUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (σ : A.decompositionSubgroup ℚ) (x : placeUnder ρ A) :
    (((σ • x : placeUnder ρ A) : splittingField ρ) : ℚbar) = (σ : Γℚ) ((x : splittingField ρ) : ℚbar) := rfl

def ramificationGroup (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) (i : ℕ) :
    Subgroup Γℚ :=
  A.inertiaSubgroupIn ℚ ⊓
    (IsLocalRing.lowerRamificationGroup (placeUnder ρ A) (A.decompositionSubgroup ℚ) i).map
      (A.decompositionSubgroup ℚ).subtype

def codimInvariants (ρ : Γℚ →* GL (Fin n) ℂ) (H : Subgroup Γℚ) : ℕ :=
  n - Module.finrank ℂ (invariantsUnder ρ H)

def swanConductor (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) : ℚ :=
  ∑ᶠ i : ℕ,
    (Nat.card ((ramificationGroup ρ A (i + 1)).map ρ) : ℚ) /
        (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ) : ℚ) *
      (codimInvariants ρ (ramificationGroup ρ A (i + 1)) : ℚ)

def conductorExponentAt (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) : ℕ :=
  codimInvariants ρ (A.inertiaSubgroupIn ℚ) + ⌈swanConductor ρ A⌉₊

open scoped Classical in

def conductorExponent (ρ : Γℚ →* GL (Fin n) ℂ) (p : ℕ) : ℕ :=
  if h : p.Prime ∧ ∃ A : ValuationSubring ℚbar, A.LiesOverPrime p then
    conductorExponentAt ρ h.2.choose
  else 0

def conductor (ρ : Γℚ →* GL (Fin n) ℂ) : ℕ :=
  ∏ᶠ p : ℕ, p ^ conductorExponent ρ p

end ArtinL

end
