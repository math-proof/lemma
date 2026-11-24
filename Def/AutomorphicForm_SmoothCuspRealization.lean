module
public import Theorem.Matrix.SmoothAutomorphicFnAt
public import Theorem.RingHom.HeckeEigensystemMap
public import Def.Set_HeckePair
public import Structure.LocalLanglands_HeckeCosetSystem
public import Structure.AutomorphicForm_SmoothCuspRealization
open IsDedekindDomain NumberField MeasureTheory Matrix
open AutomorphicForm HeckeIntegralSeam Measure RingHom Matrix


public section

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]


open SmoothCusp


def smoothCuspNotionOf
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F) :
    CuspidalityNotion ℂ where
  IsCusp := fun F _i1 _i2 Φ => Nonempty (@SmoothCuspRealizationAt F _i1 _i2 (pins F) Φ)

def IsSmoothCuspRealizable (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) : Prop :=
  Nonempty (SmoothCuspRealizationAt F pins Φ)

def IsSmoothCuspRealizableVia (pins : CarrierPins F) {R : Type*} [CommRing R]
    (ι : R →+* ℂ) (Φ : HeckeEigensystem F R) : Prop :=
  IsSmoothCuspRealizable F pins (Φ.map ι)

variable {F}

variable (F)


variable {F}

section Inhabitor

variable (F)

def degenerateZeroMeasurePins (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) : CarrierPins F where
  mS := ⊥
  μ := 0
  D := Set.univ
  Z := ⊤
  U := U
  gen := gen
  nS := ⊥
  ν := 0

def degenerateEigensystem (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) : HeckeEigensystem F ℂ where
  level := N
  level_ne_bot := hN
  a := fun v => ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 1
  b := fun _ => 1

def smoothCuspRealizationAt_one_of_cosetSystems
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (hsys : ∀ v : HeightOneSpectrum (𝓞 F),
      ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
        IsHeckeCosetSystem (U N) (gen v) reps) :
    SmoothCuspRealizationAt F (degenerateZeroMeasurePins F U gen)
      (degenerateEigensystem F N hN) where
  toFun := fun _ => 1
  exists_ne_zero := ⟨1, one_ne_zero⟩
  centralChar := 1
  smoothCusp := isSmoothCuspAutomorphicFnAt_one_zeroMeasure F U gen
  level_invariant := fun _ _ _ => rfl
  exceptionalSet := ∅
  hecke_eigen := fun v _ => by
    obtain ⟨reps, hreps⟩ := hsys v
    refine ⟨reps, hreps, fun g => ?_⟩
    rw [heckeCosetSum_const, degenerateEigensystem_a, mul_one, mul_one]
    push_cast
    ring
  central_eigen := fun v _ g => by simp only [degenerateEigensystem_b, one_mul]

end Inhabitor

end AutomorphicForm

end
