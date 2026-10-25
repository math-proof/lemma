-- Carved from Lemma/Definitions/Def_ArtinL_Conductor.lean: instance decls only.
import Mathlib
import Lemma.ArtinL.EulerFactor
import Instance.Mathlib_RingTheory_Valuation_LowerRamificationGroup
import Lemma.ArtinL.Conductor

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups Pointwise

namespace ArtinL

variable {n : ℕ}

instance mulSemiringActionSplittingField (ρ : Γℚ →* GL (Fin n) ℂ) :
    MulSemiringAction Γℚ (splittingField ρ) where
  smul σ x := ⟨σ (x : ℚbar), apply_mem_splittingField ρ σ x.2⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl
  smul_zero σ := Subtype.ext (map_zero σ)
  smul_add σ x y := Subtype.ext (map_add σ (x : ℚbar) (y : ℚbar))
  smul_one σ := Subtype.ext (map_one σ)
  smul_mul σ x y := Subtype.ext (map_mul σ (x : ℚbar) (y : ℚbar))

instance mulSemiringActionPlaceUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) :
    MulSemiringAction (A.decompositionSubgroup ℚ) (placeUnder ρ A) where
  smul σ x := ⟨(σ : Γℚ) • (x : splittingField ρ), smul_mem_placeUnder ρ A σ x.2⟩
  one_smul x := Subtype.ext (one_smul Γℚ (x : splittingField ρ))
  mul_smul σ τ x := Subtype.ext (mul_smul (σ : Γℚ) (τ : Γℚ) (x : splittingField ρ))
  smul_zero σ := Subtype.ext (smul_zero (σ : Γℚ))
  smul_add σ x y := Subtype.ext (smul_add (σ : Γℚ) (x : splittingField ρ) (y : splittingField ρ))
  smul_one σ := Subtype.ext (smul_one (σ : Γℚ))
  smul_mul σ x y :=
    Subtype.ext (MulSemiringAction.smul_mul (σ : Γℚ) (x : splittingField ρ) (y : splittingField ρ))

end ArtinL

end
