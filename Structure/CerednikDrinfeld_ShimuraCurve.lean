import Def.QuaternionAlgebra_EichlerOrder
import Def.QuaternionAlgebra_ReducedNorm
import Structure.ModularCurve_UniformizedHeckeCurve
import Lemma.Scheme.AlgebraicCurveBaseChangeGalois
import Instance.AlgebraicCurve_IsCurveOver
import Structure.CerednikDrinfeld_TwoPlaceTorsionDatum
import Instance.Compat_Mathlib430
import Instance.CerednikDrinfeld_ShimuraCurve

set_option autoImplicit false

noncomputable section

open scoped Quaternion TensorProduct MatrixGroups
open IsDedekindDomain NumberField AlgebraicCurve

namespace QuaternionAlgebra

variable (a b : ℚ)


end QuaternionAlgebra

namespace CerednikDrinfeld

open QuaternionAlgebra ModularCurve

variable {a b : ℚ}

def unitGroup (R : Submodule ℤ ℍ[ℚ, a, b]) : Subgroup (ℍ[ℚ, a, b])ˣ :=
  Subgroup.closure {u : (ℍ[ℚ, a, b])ˣ | IsUnitOf R (u : ℍ[ℚ, a, b])}

def fuchsianGroup (R : Submodule ℤ ℍ[ℚ, a, b]) (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) :
    Subgroup (GL (Fin 2) ℝ) :=
  (unitGroup R).map (Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) ℝ)) ⊓
    (Matrix.GeneralLinearGroup.det : GL (Fin 2) ℝ →* ℝˣ).ker

structure ShimuraCurveModel (R : Submodule ℤ ℍ[ℚ, a, b])
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Type 1 where

  F : Type
  [instFieldF : Field F]
  [instAlgebraF : Algebra ℚ F]

  Fbar : Type
  [instFieldFbar : Field Fbar]
  [instAlgebraFbar : Algebra (AlgebraicClosure ℚ) Fbar]

  Fc : Type
  [instFieldFc : Field Fc]
  [instAlgebraFc : Algebra ℂ Fc]

  [isCurveOverF : IsCurveOver ℚ F]

  [essFiniteTypeF : Algebra.EssFiniteType ℚ F]

  [isCurveOverBar : IsCurveOver (AlgebraicClosure ℚ) Fbar]

  [essFiniteTypeBar : Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]

  [isCurveOverC : IsCurveOver ℂ Fc]

  [essFiniteTypeC : Algebra.EssFiniteType ℂ Fc]

  algebraic_mem_range : ∀ x : F, IsAlgebraic ℚ x → x ∈ Set.range (algebraMap ℚ F)

  toBar : F →+* Fbar

  toBar_algebraMap : ∀ r : ℚ,
    toBar (algebraMap ℚ F r) = algebraMap (AlgebraicClosure ℚ) Fbar (algebraMap ℚ (AlgebraicClosure ℚ) r)

  closure_toBar : Subfield.closure
      (Set.range (algebraMap (AlgebraicClosure ℚ) Fbar) ∪ Set.range toBar) = ⊤

  linearIndependent_toBar : ∀ s : Finset F,
    LinearIndependent ℚ (fun x : s => (x : F)) →
      LinearIndependent (AlgebraicClosure ℚ) (fun x : s => toBar (x : F))

  emb : AlgebraicClosure ℚ →+* ℂ

  toC : Fbar →+* Fc

  toC_algebraMap : ∀ z : AlgebraicClosure ℚ,
    toC (algebraMap (AlgebraicClosure ℚ) Fbar z) = algebraMap ℂ Fc (emb z)

  closure_toC : Subfield.closure (Set.range (algebraMap ℂ Fc) ∪ Set.range toC) = ⊤

  linearIndependent_toC : ∀ s : Finset Fbar,
    LinearIndependent (AlgebraicClosure ℚ) (fun x : s => (x : Fbar)) →
      LinearIndependent ℂ (fun x : s => toC (x : Fbar))

  gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar

  baseAut_gal : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    SemilinearAut.baseAut (gal σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)

  gal_smul_toBar : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : F), gal σ • toBar x = toBar x

  unif : UniformizedHeckeCurve (fuchsianGroup R ι) Fc

  heckePoints_eq : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ∃ S : Finset ℍ[ℚ, a, b],
    (∀ x ∈ S, x ∈ R ∧ nrd x = ℓ ∧
      ∃ h ∈ 𝒮 ℓ, (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∧
    (∀ y : ℍ[ℚ, a, b], y ∈ R → nrd y = ℓ →
      (∃ h ∈ 𝒮 ℓ, (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = y ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) →
      ∃! x, x ∈ S ∧ ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ u * x = y) ∧
    (unif.heckePoints ℓ hℓ).map (fun g => (g : Matrix (Fin 2) (Fin 2) ℝ)) = S.val.map ι

  bcPlace : Place (AlgebraicClosure ℚ) Fbar → Place ℂ Fc

  mem_bcPlace_iff : ∀ (P : Place (AlgebraicClosure ℚ) Fbar) (x : Fbar),
    toC x ∈ (bcPlace P).toValuationSubring ↔ x ∈ P.toValuationSubring

  corrBar : ∀ ℓ : ℕ, ℓ.Prime →
    (Divisor (AlgebraicClosure ℚ) Fbar →+ Divisor (AlgebraicClosure ℚ) Fbar)

  corr_mapDomain : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (D : Divisor (AlgebraicClosure ℚ) Fbar),
    unif.corr ℓ hℓ (Finsupp.mapDomain bcPlace D) = Finsupp.mapDomain bcPlace (corrBar ℓ hℓ D)

  heckePic0 : ∀ ℓ : ℕ, ℓ.Prime → (Pic0 (AlgebraicClosure ℚ) Fbar →+ Pic0 (AlgebraicClosure ℚ) Fbar)

  heckePic0_mk : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := Fbar))
    (hD : corrBar ℓ hℓ (D : Divisor (AlgebraicClosure ℚ) Fbar) ∈
      Divisor.degZero (K := AlgebraicClosure ℚ) (F := Fbar)),
    heckePic0 ℓ hℓ (Pic0.mk D) = Pic0.mk ⟨corrBar ℓ hℓ (D : Divisor (AlgebraicClosure ℚ) Fbar), hD⟩

  heckePic0_comm : ∀ (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime),
    (heckePic0 ℓ hℓ).comp (heckePic0 ℓ' hℓ') = (heckePic0 ℓ' hℓ').comp (heckePic0 ℓ hℓ)

  gal_smul_heckePic0 : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (c : Pic0 (AlgebraicClosure ℚ) Fbar), gal σ • heckePic0 ℓ hℓ c = heckePic0 ℓ hℓ (gal σ • c)

  finite_torsion : ∀ n : ℕ, 0 < n → Finite (Pic0.torsion (AlgebraicClosure ℚ) Fbar n)

  finiteLevel_torsion : ∀ n : ℕ, 0 < n →
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) →
        ∀ c : Pic0 (AlgebraicClosure ℚ) Fbar, c ∈ Pic0.torsion (AlgebraicClosure ℚ) Fbar n → gal σ • c = c

attribute [instance] ShimuraCurveModel.instFieldF ShimuraCurveModel.instAlgebraF
  ShimuraCurveModel.instFieldFbar ShimuraCurveModel.instAlgebraFbar ShimuraCurveModel.instFieldFc
  ShimuraCurveModel.instAlgebraFc ShimuraCurveModel.isCurveOverF ShimuraCurveModel.essFiniteTypeF
  ShimuraCurveModel.isCurveOverBar ShimuraCurveModel.essFiniteTypeBar ShimuraCurveModel.isCurveOverC
  ShimuraCurveModel.essFiniteTypeC

namespace ShimuraCurveModel

variable {R : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
  {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}


end ShimuraCurveModel

end CerednikDrinfeld

end
