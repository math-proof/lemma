import Mathlib
import Lemma.Definitions.Def_AutomorphicForm_HeckeEigensystem

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

theorem infinite_heightOneSpectrum_ratO : Infinite (HeightOneSpectrum (𝓞 ℚ)) := by
  have hinj : Function.Injective
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm :=
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective
  exact Infinite.of_injective _ hinj

def zeroSatakeEigensystem : HeckeEigensystem ℚ ℂ where
  level := ⊤
  level_ne_bot := by
    intro h
    have h1 : (1 : 𝓞 ℚ) ∈ (⊥ : Ideal (𝓞 ℚ)) := h ▸ Submodule.mem_top
    exact one_ne_zero (Ideal.mem_bot.mp h1)
  a := fun _ => 0
  b := fun _ => 0

@[simp] theorem zeroSatakeEigensystem_a (v : HeightOneSpectrum (𝓞 ℚ)) :
    zeroSatakeEigensystem.a v = 0 := rfl

@[simp] theorem zeroSatakeEigensystem_b (v : HeightOneSpectrum (𝓞 ℚ)) :
    zeroSatakeEigensystem.b v = 0 := rfl

def principalShapeEigensystem : HeckeEigensystem ℚ ℂ where
  level := ⊤
  level_ne_bot := by
    intro h
    have h1 : (1 : 𝓞 ℚ) ∈ (⊥ : Ideal (𝓞 ℚ)) := h ▸ Submodule.mem_top
    exact one_ne_zero (Ideal.mem_bot.mp h1)
  a := fun _ => 2
  b := fun _ => 1

end AutomorphicForm

end
