import Mathlib
import Lemma.Gamma0HeckeOperatorHom.Main
import Instance.Gamma0CoeffCohomology
import Def.Gamma0CoeffCohomology

namespace HeckeEis

open CongruenceSubgroup
open scoped MatrixGroups

section Cocycles

variable {G : Type*} [Group G] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]


theorem mem_coeffCocycles_iff (ρ : Representation K G V) (z : G → V) :
    z ∈ coeffCocycles ρ ↔ ∀ g h : G, z (g * h) = z g + ρ g (z h) :=
  Iff.rfl


@[simp]
theorem coeffCoboundaryMap_apply (ρ : Representation K G V) (v : V) (g : G) :
    coeffCoboundaryMap ρ v g = ρ g v - v :=
  rfl


theorem mem_coeffCoboundaries_iff (ρ : Representation K G V) (z : G → V) :
    z ∈ coeffCoboundaries ρ ↔ ∃ v : V, (fun g => ρ g v - v) = z := by
  simp [coeffCoboundaries, LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [← hv]; rfl⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [← hv]; rfl⟩

theorem coeffCoboundaries_le_coeffCocycles (ρ : Representation K G V) :
    coeffCoboundaries ρ ≤ coeffCocycles ρ := by
  rintro z ⟨v, rfl⟩ g h
  show ρ (g * h) v - v = (ρ g v - v) + ρ g (ρ h v - v)
  rw [map_mul, map_sub]
  simp only [Module.End.mul_apply]
  abel

end Cocycles

section Parabolic

variable {Γ : Subgroup SL(2, ℤ)} {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]


theorem mem_coeffParabolicCocycles_iff (ρ : Representation K Γ V) (z : Γ → V) :
    z ∈ coeffParabolicCocycles ρ ↔ z ∈ coeffCocycles ρ ∧ IsParabolicCocycle ρ z :=
  Iff.rfl

theorem coeffParabolicCocycles_le_coeffCocycles (ρ : Representation K Γ V) :
    coeffParabolicCocycles ρ ≤ coeffCocycles ρ :=
  fun _ hz => hz.1

theorem coeffCoboundaries_le_coeffParabolicCocycles (ρ : Representation K Γ V) :
    coeffCoboundaries ρ ≤ coeffParabolicCocycles ρ := by
  intro z hz
  refine ⟨coeffCoboundaries_le_coeffCocycles ρ hz, fun γ _ => ?_⟩
  obtain ⟨v, rfl⟩ := hz
  exact ⟨v, by simp [coeffCoboundaryMap]⟩


theorem coeffH1parMk_surjective (ρ : Representation K Γ V) :
    Function.Surjective (coeffH1parMk ρ) :=
  Submodule.mkQ_surjective _

theorem coeffH1parMk_eq_zero_iff (ρ : Representation K Γ V) (z : ↥(coeffParabolicCocycles ρ)) :
    coeffH1parMk ρ z = 0 ↔ (z : Γ → V) ∈ coeffCoboundaries ρ :=
  (Submodule.Quotient.mk_eq_zero _).trans Submodule.mem_comap

end Parabolic

section Hecke

variable (N : ℕ) (ℓ : ℕ) [NeZero ℓ]
variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]


theorem coeffHeckeFun_apply (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
    (z : Gamma0 N → V) (g : Gamma0 N) :
    coeffHeckeFun N ℓ ρ a z g =
      letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
      ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
        ρ (g • q).out (a (z (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q)))) :=
  rfl

theorem coeffHeckeFun_trivial (φ : Additive (Gamma0 N) →+ K) (g : Gamma0 N) :
    coeffHeckeFun N ℓ (1 : Representation K (Gamma0 N) K) LinearMap.id
        (fun h => φ (Additive.ofMul h)) g
      = heckeOperatorHom N ℓ K φ (Additive.ofMul g) := by
  rw [coeffHeckeFun_apply, heckeOperatorHom_apply]
  simp

end Hecke

end HeckeEis
