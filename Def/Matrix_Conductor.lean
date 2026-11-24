module
public import Mathlib
public import Def.Matrix_EulerFactor
public import Theorem.Ideal.Valuation.LowerRamificationGroup
public import Instance.ArtinL_Conductor
public import Notation.ArtinL_Conductor
set_option autoImplicit false


public section

noncomputable section

open scoped MatrixGroups Pointwise

namespace ArtinL

variable {n : ℕ}

open scoped ArtinL_Conductor

def splittingField (ρ : Γℚ →* GL (Fin n) ℂ) : IntermediateField ℚ ℚbar :=
  IntermediateField.fixedField ρ.ker

def placeUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) :
    ValuationSubring (splittingField ρ) :=
  A.comap (algebraMap (splittingField ρ) ℚbar)

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
