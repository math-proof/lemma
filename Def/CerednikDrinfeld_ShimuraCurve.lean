module

public import Theorem.QuaternionAlgebra.EichlerOrder
public import Theorem.QuaternionAlgebra.ReducedNorm
public import Def.ModularCurve_UniformizedHeckeCurve
public import Theorem.Scheme.AlgebraicCurveBaseChangeGalois
public import Instance.AlgebraicCurve_IsCurveOver
public import Structure.CerednikDrinfeld_TwoPlaceTorsionDatum
public import Def.Ideal_Mathlib430
public import Instance.CerednikDrinfeld_ShimuraCurve
public import Structure.CerednikDrinfeld_ShimuraCurve
public import Abbrev.CerednikDrinfeld_ShimuraCurve

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped Quaternion TensorProduct MatrixGroups
open IsDedekindDomain NumberField AlgebraicCurve

namespace QuaternionAlgebra

variable (a b : ℚ)

def IsIndefiniteRamifiedExactlyAt (q q' : ℕ) : Prop :=
  (0 < a ∨ 0 < b) ∧
    ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
        ((q : 𝓞 ℚ) ∈ v.asIdeal ∨ (q' : 𝓞 ℚ) ∈ v.asIdeal)

end QuaternionAlgebra

namespace CerednikDrinfeld

open QuaternionAlgebra ModularCurve

variable {a b : ℚ}


namespace ShimuraCurveModel

variable {R : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
  {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

def heckeGenJ (M : ShimuraCurveModel R ι 𝒮) (ℓ : Nat.Primes) : Module.End ℤ M.J :=
  (M.heckePic0 ℓ ℓ.prop).toIntLinearMap

@[reducible] def commRingAdjoinJ (M : ShimuraCurveModel R ι 𝒮) :
    CommRing ↥(Algebra.adjoin ℤ (Set.range M.heckeGenJ)) :=
  { (inferInstance : Ring ↥(Algebra.adjoin ℤ (Set.range M.heckeGenJ))) with
    mul_comm := M.isMulCommutative_adjoin_heckeGenJ.is_comm.comm }

def heckeJAux (M : ShimuraCurveModel R ι 𝒮) :
    HeckeAlg →ₐ[ℤ] (Algebra.adjoin ℤ (Set.range M.heckeGenJ) : Subalgebra ℤ (Module.End ℤ M.J)) :=
  letI : CommSemiring ↥(Algebra.adjoin ℤ (Set.range M.heckeGenJ)) := M.commRingAdjoinJ.toCommSemiring
  MvPolynomial.aeval fun ℓ =>
    (⟨M.heckeGenJ ℓ, Algebra.subset_adjoin (Set.mem_range_self ℓ)⟩ : Algebra.adjoin ℤ (Set.range M.heckeGenJ))

def heckeJ (M : ShimuraCurveModel R ι 𝒮) : HeckeAlg →+* Module.End ℤ M.J :=
  ((Algebra.adjoin ℤ (Set.range M.heckeGenJ)).val.comp M.heckeJAux).toRingHom

def galJ (M : ShimuraCurveModel R ι 𝒮) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut M.J :=
  (DistribMulAction.toAddAut' (SemilinearAut (AlgebraicClosure ℚ) M.Fbar) M.J).comp M.gal

def signTwist (ε : Nat.Primes → ℤˣ) : HeckeAlg →+* HeckeAlg :=
  (MvPolynomial.aeval fun ℓ => ((ε ℓ : ℤ) : HeckeAlg) * MvPolynomial.X ℓ).toRingHom

abbrev heckeJSigned (M : ShimuraCurveModel R ι 𝒮) (ε : Nat.Primes → ℤˣ) : HeckeAlg →+* Module.End ℤ M.J :=
  M.heckeJ.comp (signTwist ε)

def GoodReductionOutside (M : ShimuraCurveModel R ι 𝒮) (p S : ℕ) : Prop :=
  (∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ S →
    ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
      ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ t : M.J, p • t = 0 → M.galJ σ t = t) ∧
  (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ S →
    ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, B.IsFrobeniusAt σ ℓ →
        ∀ t : M.J, p • t = 0 →
          M.galJ σ (M.galJ σ t) - M.heckeJ (heckeGen ⟨ℓ, hℓ⟩) (M.galJ σ t) + ℓ • t = 0)

def restrictTors (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) : Module.End ℤ M.J →+* Module.End ℤ (M.Tors p) where
  toFun f := f.restrict (p := (Pic0.torsion (AlgebraicClosure ℚ) M.Fbar p).toIntSubmodule)
    (q := (Pic0.torsion (AlgebraicClosure ℚ) M.Fbar p).toIntSubmodule) (fun x hx => by
      change x ∈ Pic0.torsion (AlgebraicClosure ℚ) M.Fbar p at hx
      change f x ∈ Pic0.torsion (AlgebraicClosure ℚ) M.Fbar p
      rw [Pic0.mem_torsion] at hx ⊢
      rw [← map_zsmul, hx, map_zero])
  map_one' := by apply LinearMap.ext; intro t; rfl
  map_mul' f g := by apply LinearMap.ext; intro t; rfl
  map_zero' := by apply LinearMap.ext; intro t; rfl
  map_add' f g := by apply LinearMap.ext; intro t; rfl

def torsionHecke (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) : HeckeAlg →+* Module.End ℤ (M.Tors p) :=
  (M.restrictTors p).comp M.heckeJ

def torsionGal (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut (M.Tors p) :=
  (DistribMulAction.toAddAut' (SemilinearAut (AlgebraicClosure ℚ) M.Fbar) (M.Tors p)).comp M.gal

def IsTorsionOf (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) (T : Type) [AddCommGroup T]
    (hecke : HeckeAlg →+* Module.End ℤ T)
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T) : Prop :=
  ∃ e : T →+ M.J, Function.Injective e ∧ e.range = Pic0.torsion (AlgebraicClosure ℚ) M.Fbar p ∧
    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : T), e (gal σ t) = M.gal σ • e t) ∧
    ∀ (ℓ : Nat.Primes) (t : T), e (hecke (heckeGen ℓ) t) = M.heckePic0 ℓ ℓ.prop (e t)

def RealizesJPrime (M : ShimuraCurveModel R ι 𝒮) {p : ℕ} {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
    {A : ValuationSubring (AlgebraicClosure ℚ)} (Dm : JPrimeTorsionDatum p E V A) : Prop :=
  M.IsTorsionOf p Dm.T Dm.hecke Dm.gal

def RealizesTwoPlace (M : ShimuraCurveModel R ι 𝒮) {p : ℕ} {E₁ V₁ E₂ V₂ : Type}
    [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂}
    {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)} (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : Prop :=
  M.IsTorsionOf p 𝒥.T 𝒥.hecke 𝒥.gal

end ShimuraCurveModel

end CerednikDrinfeld

end

end
