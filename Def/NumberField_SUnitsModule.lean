import Mathlib
import Theorem.Matrix.PlaceAbove
import Def.NumberField_PlaceDecompositionAction
import Abbrev.NumberField_SUnitsModule

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory Matrix Valuation
open scoped NumberField.PlaceDecomp

namespace NumberField.SUnits

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

omit [NumberField K] in

def placesAbove (S : Finset (HeightOneSpectrum (𝓞 E))) : Set (HeightOneSpectrum (𝓞 K)) := {w | w.under (𝓞 E) ∈ S}

omit [NumberField E] [NumberField K] in
noncomputable def sUnits (S : Finset (HeightOneSpectrum (𝓞 E))) : Subgroup Kˣ :=
  ⨅ σ : K ≃ₐ[E] K, (Set.unit (placesAbove E K S) K).comap (Units.map (σ : K →* K))

omit [NumberField E] in
noncomputable def sUnitsSubmodule (S : Finset (HeightOneSpectrum (𝓞 E))) : Submodule ℤ (Additive Kˣ) :=
  (Subgroup.toAddSubgroup (sUnits E K S)).toIntSubmodule

omit [NumberField E] in
noncomputable abbrev sUnitsRep (S : Finset (HeightOneSpectrum (𝓞 E))) : Rep ℤ (K ≃ₐ[E] K) :=
  Rep.of ((Representation.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ).subrepresentation (sUnitsSubmodule E K S)
    fun σ x hx => by
      have hx' : Additive.toMul x ∈ sUnits E K S := (mem_sUnitsSubmodule E K S x).1 hx
      have hρ := Representation.ofMulDistribMulAction_apply_apply
        (M := K ≃ₐ[E] K) (G := Kˣ) σ x
      have : Additive.toMul
          (Representation.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ σ x)
          ∈ sUnits E K S := by
        rw [hρ, toMul_ofMul]
        exact smul_mem_sUnits E K S σ hx'
      exact (mem_sUnitsSubmodule E K S _).2 this)

noncomputable def toUnitsRep (S : Finset (HeightOneSpectrum (𝓞 E))) : sUnitsRep E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ :=
  Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

section diag
variable (S : Finset (HeightOneSpectrum (𝓞 E)))

abbrev val (x : sUnitsSubmodule E K S) : Kˣ := Additive.toMul x.1

omit [NumberField E] in
noncomputable def diagFun (v : HeightOneSpectrum (𝓞 E)) :
    sUnitsRep E K S →ₗ[ℤ] ((K ≃ₐ[E] K) → Additive ((Matrix.PlaceAbove.above E K v).adicCompletion K)ˣ) where
  toFun x g := Additive.ofMul (Units.map (loc E K v).toMonoidHom (g • val E K S x))
  map_add' x y := by
    funext g
    change Additive.ofMul (Units.map (loc E K v).toMonoidHom (g • (val E K S x * val E K S y))) = _
    rw [smul_mul', map_mul, ofMul_mul]
    rfl
  map_smul' n x := by
    funext g
    change Additive.ofMul (Units.map (loc E K v).toMonoidHom (g • (val E K S x ^ n))) = _
    rw [smul_zpow', map_zpow, ofMul_zpow]
    rfl

end diag

end NumberField.SUnits
