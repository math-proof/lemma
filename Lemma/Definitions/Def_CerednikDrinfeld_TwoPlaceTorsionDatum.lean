import Lemma.Definitions.Def_CerednikDrinfeld_JPrimeTorsionDatum
import Lemma.Definitions.Def_Compat_Mathlib430

set_option autoImplicit false

namespace CerednikDrinfeld

open ModularCurve

namespace JPrimeTorsionDatum

variable {p : ℕ} {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
  {A : ValuationSubring (AlgebraicClosure ℚ)}

structure LocalLaws (Dm : JPrimeTorsionDatum p E V A) (r : ℕ) [Fact r.Prime] : Prop where

  toric_hecke : ∀ (x : HeckeAlg) (t : Dm.T), t ∈ Dm.toric → Dm.hecke x t ∈ Dm.toric

  toricEquiv_hecke : ∀ (ℓ : Nat.Primes) (t : Dm.T) (ht : t ∈ Dm.toric)
      (hℓt : Dm.hecke (heckeGen ℓ) t ∈ Dm.toric),
      Dm.toricEquiv ⟨Dm.hecke (heckeGen ℓ) t, hℓt⟩ = (Dm.toricEquiv ⟨t, ht⟩) ∘ₗ heckeKernelMap Dm.H ℓ

  toric_le_invariants : Dm.toric ≤ Dm.invariants

  sp_eq_zero_iff : ∀ t : ↥Dm.invariants, Dm.sp t = 0 ↔ (t : Dm.T) ∈ Dm.toric

  mem_range_sp_iff : ∀ ψ : ribbonComponentGroup Dm.D, ψ ∈ Dm.sp.range ↔ p • ψ = 0

  sp_hecke : ∀ (ℓ : Nat.Primes) (t : ↥Dm.invariants)
      (hℓt : Dm.hecke (heckeGen ℓ) (t : Dm.T) ∈ Dm.invariants)
      (φ : Module.Dual ℤ ↥(ribbonKernel Dm.D)),
      Dm.sp t = ribbonComponentGroupProj Dm.D φ →
        Dm.sp ⟨Dm.hecke (heckeGen ℓ) (t : Dm.T), hℓt⟩ =
          ribbonComponentGroupProj Dm.D (φ ∘ₗ heckeKernelMap Dm.H ℓ)

  sp_hecke_ringHom : ∀ (heckeΨ : HeckeAlg →+* Module.End ℤ (ribbonComponentGroup Dm.D)),
      (∀ (ℓ : Nat.Primes) (φ : Module.Dual ℤ ↥(ribbonKernel Dm.D)),
          heckeΨ (heckeGen ℓ) (ribbonComponentGroupProj Dm.D φ) =
            ribbonComponentGroupProj Dm.D (φ ∘ₗ heckeKernelMap Dm.H ℓ)) →
        ∀ (x : HeckeAlg) (t : ↥Dm.invariants) (ht : Dm.hecke x (t : Dm.T) ∈ Dm.invariants),
          Dm.sp ⟨Dm.hecke x (t : Dm.T), ht⟩ = heckeΨ x (Dm.sp t)

  frobenius_toric : ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ r →
      ∀ t : Dm.T, t ∈ Dm.toric → Dm.gal φ t = Dm.hecke ((r : HeckeAlg) * heckeGen ⟨r, Fact.out⟩) t

  frobenius_quot : ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ r →
      ∀ t : Dm.T, Dm.gal φ t - Dm.hecke (heckeGen ⟨r, Fact.out⟩) t ∈ Dm.toric

structure GoodReductionOutside (Dm : JPrimeTorsionDatum p E V A) (M : ℕ) : Prop where

  unramified : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ ∈ B.inertiaSubgroupIn ℚ, Dm.gal σ = 1

  eichlerShimura : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, B.IsFrobeniusAt σ ℓ →
          ∀ t : Dm.T, Dm.gal σ (Dm.gal σ t) - Dm.hecke (heckeGen ⟨ℓ, hℓ⟩) (Dm.gal σ t) + ℓ • t = 0

end JPrimeTorsionDatum

structure TwoPlaceTorsionDatum (p : ℕ) {E₁ V₁ E₂ V₂ : Type}
    [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    (D₁ : DegeneracyData E₁ V₁) (H₁ : HeckeData D₁) (D₂ : DegeneracyData E₂ V₂) (H₂ : HeckeData D₂)
    (A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)) : Type 1 where

  T : Type
  [instAddCommGroup : AddCommGroup T]
  [instFinite : Finite T]

  pTorsion : ∀ t : T, p • t = 0

  hecke : HeckeAlg →+* Module.End ℤ T

  gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T

  comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
    gal σ (hecke x t) = hecke x (gal σ t)

  finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → gal σ = 1

  toric₁ : AddSubgroup T

  toricEquiv₁ : ↥toric₁ ≃+ (↥(ribbonKernel D₁) →ₗ[ℤ] ZMod p)

  sp₁ : ↥(⨅ σ ∈ A₁.inertiaSubgroupIn ℚ, ((gal σ).toAddMonoidHom - AddMonoidHom.id T).ker) →+
    ribbonComponentGroup D₁

  toric₂ : AddSubgroup T

  toricEquiv₂ : ↥toric₂ ≃+ (↥(ribbonKernel D₂) →ₗ[ℤ] ZMod p)

  sp₂ : ↥(⨅ σ ∈ A₂.inertiaSubgroupIn ℚ, ((gal σ).toAddMonoidHom - AddMonoidHom.id T).ker) →+
    ribbonComponentGroup D₂

attribute [instance] TwoPlaceTorsionDatum.instAddCommGroup TwoPlaceTorsionDatum.instFinite

namespace TwoPlaceTorsionDatum

variable {p : ℕ} {E₁ V₁ E₂ V₂ : Type}
  [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
  {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂}
  {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)}

def fst (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : JPrimeTorsionDatum p E₁ V₁ A₁ where
  D := D₁
  H := H₁
  T := 𝒥.T
  pTorsion := 𝒥.pTorsion
  hecke := 𝒥.hecke
  gal := 𝒥.gal
  comm := 𝒥.comm
  finiteLevel := 𝒥.finiteLevel
  toric := 𝒥.toric₁
  toricEquiv := 𝒥.toricEquiv₁
  sp := 𝒥.sp₁

def snd (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : JPrimeTorsionDatum p E₂ V₂ A₂ where
  D := D₂
  H := H₂
  T := 𝒥.T
  pTorsion := 𝒥.pTorsion
  hecke := 𝒥.hecke
  gal := 𝒥.gal
  comm := 𝒥.comm
  finiteLevel := 𝒥.finiteLevel
  toric := 𝒥.toric₂
  toricEquiv := 𝒥.toricEquiv₂
  sp := 𝒥.sp₂

@[simp] theorem fst_D (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.fst.D = D₁ := rfl
@[simp] theorem snd_D (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.snd.D = D₂ := rfl
@[simp] theorem fst_T (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.fst.T = 𝒥.T := rfl
@[simp] theorem snd_T (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.snd.T = 𝒥.T := rfl
@[simp] theorem fst_toric (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.fst.toric = 𝒥.toric₁ := rfl
@[simp] theorem snd_toric (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.snd.toric = 𝒥.toric₂ := rfl

structure Laws (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) (M r₁ r₂ : ℕ)
    [Fact r₁.Prime] [Fact r₂.Prime] : Prop where

  goodReduction : 𝒥.fst.GoodReductionOutside M

  fst : 𝒥.fst.LocalLaws r₁

  snd : 𝒥.snd.LocalLaws r₂

end TwoPlaceTorsionDatum

end CerednikDrinfeld
