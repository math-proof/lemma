module

public import Mathlib
public import Theorem.Matrix.PlaceAbove
public import Theorem.Valuation.PlaceDecompositionAction
public import Abbrev.NumberField_SUnitsModule

public section

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory Matrix Valuation
open scoped NumberField.PlaceDecomp

namespace NumberField.SUnits

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

omit [NumberField K] in

public theorem under_above (v : HeightOneSpectrum (𝓞 E)) : (Matrix.PlaceAbove.above E K v).under (𝓞 E) = v :=
  HeightOneSpectrum.ext (Matrix.PlaceAbove.comap_above E K v)


public theorem mem_placesAbove (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 K)) : w ∈ placesAbove E K S ↔ w.under (𝓞 E) ∈ S :=
  Iff.rfl


public theorem mem_sUnits_iff (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Kˣ) :
    x ∈ sUnits E K S ↔ ∀ σ : K ≃ₐ[E] K, ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S → w.valuation K (σ (x : K)) = 1 := by
  simp only [sUnits, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact forall_congr' fun σ => Iff.rfl

omit [NumberField E] in

public theorem smul_mem_sUnits (S : Finset (HeightOneSpectrum (𝓞 E))) (τ : K ≃ₐ[E] K) {x : Kˣ} (hx : x ∈ sUnits E K S) : τ • x ∈ sUnits E K S := by
  rw [mem_sUnits_iff] at hx ⊢
  intro σ w hw
  exact hx (σ * τ) w hw


public theorem valuation_eq_one_of_mem_sUnits (S : Finset (HeightOneSpectrum (𝓞 E))) {x : Kˣ} (hx : x ∈ sUnits E K S) (σ : K ≃ₐ[E] K)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∉ S) :
    (Matrix.PlaceAbove.above E K v).valuation K (σ (x : K)) = 1 :=
  (mem_sUnits_iff E K S x).1 hx σ _ (by rwa [under_above])


public theorem mem_sUnitsSubmodule (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Additive Kˣ) :
    x ∈ sUnitsSubmodule E K S ↔ Additive.toMul x ∈ sUnits E K S := Iff.rfl


public theorem smul_loc (v : HeightOneSpectrum (𝓞 E)) (σ : NumberField.PlaceDecomp.decomp E K (Matrix.PlaceAbove.above E K v)) (x : K) :
    σ • loc E K v x = loc E K v ((σ : K ≃ₐ[E] K) x) := by
  rw [NumberField.PlaceDecomp.smul_def, show loc E K v = algebraMap K _ from rfl,
    IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [NumberField.PlaceDecomp.actRingEquiv_coe, WithVal.congr_apply]
  rfl


public theorem valued_loc (v : HeightOneSpectrum (𝓞 E)) (x : K) :
    Valued.v (loc E K v x) = (Matrix.PlaceAbove.above E K v).valuation K x := by
  rw [show loc E K v = algebraMap K _ from rfl, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ x


@[simp] public theorem val_add (x y : sUnitsRep E K S) : val E K S (x + y) = val E K S x * val E K S y := rfl
omit [NumberField E] in

@[simp] public theorem val_zsmul (n : ℤ) (x : sUnitsRep E K S) : val E K S (n • x) = val E K S x ^ n := rfl
omit [NumberField E] in

public theorem val_mem (x : sUnitsRep E K S) : val E K S x ∈ sUnits E K S := Subtype.property (x : sUnitsSubmodule E K S)
omit [NumberField E] in

public theorem val_rho (σ : K ≃ₐ[E] K) (x : sUnitsRep E K S) : val E K S ((sUnitsRep E K S).ρ σ x) = σ • val E K S x := rfl


public theorem diagFun_apply (v : HeightOneSpectrum (𝓞 E)) (x : sUnitsRep E K S) (g : K ≃ₐ[E] K) :
    diagFun E K S v x g = Additive.ofMul (Units.map (loc E K v).toMonoidHom (g • val E K S x)) := rfl

end diag

end NumberField.SUnits
