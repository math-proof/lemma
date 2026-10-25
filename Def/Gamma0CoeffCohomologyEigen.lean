import Mathlib
import Instance.Gamma0CoeffCohomology
import Lemma.HeckeEis.BinaryFormRep
import Instance.Gamma0CoeffCohomologyEigen

set_option autoImplicit false

namespace HeckeEis

open CongruenceSubgroup
open scoped MatrixGroups

section H1

variable {G : Type*} [Group G] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

def coeffH1 (ρ : Representation K G V) : Type _ :=
  ↥(coeffCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype

def coeffH1Mk (ρ : Representation K G V) : ↥(coeffCocycles ρ) →ₗ[K] coeffH1 ρ :=
  ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype).mkQ

end H1

section Parabolic

variable {Γ : Subgroup SL(2, ℤ)} {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

def coeffH1parToH1 (ρ : Representation K Γ V) : coeffH1par ρ →ₗ[K] coeffH1 ρ :=
  ((coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype).mapQ
    ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype)
    (Submodule.inclusion (coeffParabolicCocycles_le_coeffCocycles ρ))
    fun _ hz => hz

end Parabolic

section Hecke

variable (N : ℕ) (ℓ : ℕ) [NeZero ℓ]
variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

def IsCoeffHeckeOnH1 (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
    (T : coeffH1 ρ →ₗ[K] coeffH1 ρ) : Prop :=
  ∀ z : ↥(coeffCocycles ρ), ∃ w : ↥(coeffCocycles ρ),
    (w : Gamma0 N → V) = coeffHeckeFun N ℓ ρ a z ∧ T (coeffH1Mk ρ z) = coeffH1Mk ρ w

end Hecke

section Eigensystem

variable (N : ℕ) {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

def IsEigensystemH1 (ρ : Representation K (Gamma0 N) V) (a : ℕ → (V →ₗ[K] V)) (S₀ : Set ℕ)
    (lam : ℕ → K) : Prop :=
  ∃ x : coeffH1 ρ, x ≠ 0 ∧ ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
    ∃ T : coeffH1 ρ →ₗ[K] coeffH1 ρ,
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; IsCoeffHeckeOnH1 N ℓ ρ (a ℓ) T) ∧ T x = lam ℓ • x

end Eigensystem

section BinaryFormRep

variable (K : Type*) [CommRing K] (n : ℕ)

noncomputable def binaryFormRep : Matrix (Fin 2) (Fin 2) ℤ →* (↥(BinaryForm K n) →ₗ[K] ↥(BinaryForm K n)) where
  toFun M := (binarySubst K M).toLinearMap.restrict fun _ hF => binarySubst_mem K M hF
  map_one' := by
    refine LinearMap.ext fun F => Subtype.ext ?_
    change binarySubst K (1 : Matrix (Fin 2) (Fin 2) ℤ) F.1 = F.1
    rw [binarySubst_one]
    rfl
  map_mul' M M' := by
    refine LinearMap.ext fun F => Subtype.ext ?_
    change binarySubst K (M * M') F.1 = binarySubst K M (binarySubst K M' F.1)
    rw [binarySubst_mul]
    rfl

end BinaryFormRep

end HeckeEis
