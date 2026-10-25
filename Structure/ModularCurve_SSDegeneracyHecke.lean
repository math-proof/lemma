import Lemma.ModularCurve.CharLDegeneracyHecke
import Def.ModularCurve_PlaceWidth
import Structure.CerednikDrinfeld_Ribbon

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section LevelLegs

variable (K : Type*) [Field K] (M s : ℕ) [NeZero M] [NeZero s]

theorem modularFunctionFieldC_le_of_mem (hM : jqNModC K M ∈ modularFunctionFieldC K (M * s)) :
    modularFunctionFieldC K M ≤ modularFunctionFieldC K (M * s) := by
  show IntermediateField.adjoin K {jqModC K, jqNModC K M} ≤ _
  refine IntermediateField.adjoin_le_iff.mpr ?_
  intro x hx
  rcases hx with h | h
  · subst h
    exact jqModC_mem K (M * s)
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact hM

theorem map_qExpandAlgC_le_of_mem (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s)) :
    (modularFunctionFieldC K M).map (qExpandAlgC K s) ≤ modularFunctionFieldC K (M * s) := by
  show (IntermediateField.adjoin K {jqModC K, jqNModC K M}).map (qExpandAlgC K s) ≤ _
  rw [IntermediateField.adjoin_map]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x hx
  simp only [Set.image_insert_eq, Set.image_singleton, qExpandAlgC_apply] at hx
  rcases hx with h | h
  · subst h
    exact hS
  · rw [Set.mem_singleton_iff] at h
    subst h
    show qExpand K s (jqNModC K M) ∈ modularFunctionFieldC K (M * s)
    unfold jqNModC
    rw [qExpand_qExpand]
    simp only [Nat.mul_comm s M]
    exact jqNModC_mem K (M * s)

def levelAlphaC (hM : jqNModC K M ∈ modularFunctionFieldC K (M * s)) :
    modularFunctionFieldC K M →ₐ[K] modularFunctionFieldC K (M * s) :=
  IntermediateField.inclusion (modularFunctionFieldC_le_of_mem K M s hM)

@[simp]

def levelBetaCRingHom (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s)) :
    modularFunctionFieldC K M →+* modularFunctionFieldC K (M * s) where
  toFun x := ⟨qExpand K s (x : LaurentSeries K), map_qExpandAlgC_le_of_mem K M s hS ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (qExpand K s))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand K s) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand K s))
  map_add' _ _ := Subtype.ext (map_add (qExpand K s) _ _)

def levelBetaC (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s)) :
    modularFunctionFieldC K M →ₐ[K] modularFunctionFieldC K (M * s) :=
  { levelBetaCRingHom K M s hS with
    commutes' := fun a => Subtype.ext <| by
      show qExpand K s (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) a
      rw [algebraMap_laurentSeries_apply_eq_single, qExpand_single, mul_zero] }

@[simp]

def IsAtkinLehnerLevelAut (hM : jqNModC K M ∈ modularFunctionFieldC K (M * s))
    (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s))
    (σ : modularFunctionFieldC K (M * s) ≃ₐ[K] modularFunctionFieldC K (M * s)) : Prop :=
  σ (jGeomGen K (M * s)) = ⟨jqNModC K s, hS⟩ ∧ σ ⟨jqNModC K s, hS⟩ = jGeomGen K (M * s) ∧
    σ (jNGeomGen K (M * s)) = ⟨jqNModC K M, hM⟩ ∧ σ ⟨jqNModC K M, hM⟩ = jNGeomGen K (M * s)

def autOnPlaces (σ : modularFunctionFieldC K (M * s) ≃ₐ[K] modularFunctionFieldC K (M * s)) :
    Place K (modularFunctionFieldC K (M * s)) ≃ Place K (modularFunctionFieldC K (M * s)) :=
  Place.congrEquiv σ.toRingEquiv (fun c => σ.commutes c)

end LevelLegs

section Matrices

variable (p : ℕ) (K : Type*) [Field K] [DecidableEq K] (N : ℕ) [NeZero N]

open Classical in


variable [Fact p.Prime] [CharP K p]

open Classical in


end Matrices

section Datum

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [DecidableEq K] (M s : ℕ) [NeZero M] [NeZero s]

structure SSLevelDatum where

  mem_M : jqNModC K M ∈ modularFunctionFieldC K (M * s)

  mem_s : jqNModC K s ∈ modularFunctionFieldC K (M * s)

  fstIntegral : (levelAlphaC K M s mem_M).toRingHom.IsIntegral

  sndIntegral : (levelBetaC K M s mem_s).toRingHom.IsIntegral

  legsIntegral : ∀ (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ],
    (heckeAlphaC K N ℓ).toRingHom.IsIntegral ∧ (heckeBetaC K N ℓ).toRingHom.IsIntegral

  fst_mem : ∀ W, W ∈ ssPlaces p (M * s) K →
    Place.restrictAlong (levelAlphaC K M s mem_M) fstIntegral W ∈ ssPlaces p M K

  snd_mem : ∀ W, W ∈ ssPlaces p (M * s) K →
    Place.restrictAlong (levelBetaC K M s mem_s) sndIntegral W ∈ ssPlaces p M K

  atkinLehnerAut : modularFunctionFieldC K (M * s) ≃ₐ[K] modularFunctionFieldC K (M * s)
  isAtkinLehner : IsAtkinLehnerLevelAut K M s mem_M mem_s atkinLehnerAut

  stable : ∀ W, W ∈ ssPlaces p (M * s) K → autOnPlaces K M s atkinLehnerAut W ∈ ssPlaces p (M * s) K

  frobData : ModularPolynomialData p

  kronecker : KroneckerCongruence p frobData

namespace SSLevelDatum

variable {p K M s}
variable (X : SSLevelDatum p K M s)


section Laws

variable [Fact s.Prime] [Fintype ↥(ssPlaces p (M * s) K)] [Fintype ↥(ssPlaces p M K)] [DecidableEq ↥(ssPlaces p M K)]


open Classical in


end Laws

end SSLevelDatum

end Datum

end ModularCurve

end
