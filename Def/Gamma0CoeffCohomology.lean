import Mathlib
import Instance.Gamma0HeckeOperatorHom
import Instance.Gamma0CoeffCohomology

namespace HeckeEis

open CongruenceSubgroup
open scoped MatrixGroups

section Cocycles

variable {G : Type*} [Group G] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

def coeffCocycles (ρ : Representation K G V) : Submodule K (G → V) where
  carrier := {z | ∀ g h : G, z (g * h) = z g + ρ g (z h)}
  zero_mem' := by
    intro g h
    simp
  add_mem' := by
    intro z w hz hw g h
    simp only [Pi.add_apply, hz g h, hw g h, map_add]
    abel
  smul_mem' := by
    intro c z hz g h
    simp only [Pi.smul_apply, hz g h, smul_add, map_smul]


def coeffCoboundaryMap (ρ : Representation K G V) : V →ₗ[K] (G → V) where
  toFun v := fun g => ρ g v - v
  map_add' v w := by
    ext g
    simp only [map_add, Pi.add_apply]
    abel
  map_smul' c v := by
    ext g
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_sub]


def coeffCoboundaries (ρ : Representation K G V) : Submodule K (G → V) :=
  LinearMap.range (coeffCoboundaryMap ρ)

end Cocycles

section Parabolic

variable {Γ : Subgroup SL(2, ℤ)} {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

def IsParabolicCocycle (ρ : Representation K Γ V) (z : Γ → V) : Prop :=
  ∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
    z γ ∈ LinearMap.range (ρ γ - 1)

def coeffParabolicCocycles (ρ : Representation K Γ V) : Submodule K (Γ → V) where
  carrier := {z | z ∈ coeffCocycles ρ ∧ IsParabolicCocycle ρ z}
  zero_mem' := ⟨Submodule.zero_mem _, fun γ _ => by simp⟩
  add_mem' := by
    rintro z w ⟨hz, hz'⟩ ⟨hw, hw'⟩
    exact ⟨Submodule.add_mem _ hz hw, fun γ hγ => Submodule.add_mem _ (hz' γ hγ) (hw' γ hγ)⟩
  smul_mem' := by
    rintro c z ⟨hz, hz'⟩
    exact ⟨Submodule.smul_mem _ c hz, fun γ hγ => Submodule.smul_mem _ c (hz' γ hγ)⟩


def coeffH1par (ρ : Representation K Γ V) : Type _ :=
  ↥(coeffParabolicCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype

def coeffH1parMk (ρ : Representation K Γ V) : ↥(coeffParabolicCocycles ρ) →ₗ[K] coeffH1par ρ :=
  ((coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype).mkQ

end Parabolic

section Hecke

variable (N : ℕ) (ℓ : ℕ) [NeZero ℓ]
variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def coeffHeckeFun (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
    (z : Gamma0 N → V) : Gamma0 N → V :=
  fun g =>
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
      ρ (g • q).out (a (z (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q))))

end Hecke

end HeckeEis
