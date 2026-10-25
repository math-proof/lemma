import Def.LanglandsTunnell_CubicInduction_GlobalZeta31
import Lemma.AdelicDock.LocalEmbedding
import Structure.LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Embeddings

variable (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]


variable (v : HeightOneSpectrum R)


end Embeddings

section LocalThree

variable (v : HeightOneSpectrum (𝓞 ℚ))


theorem one_mem_converseCongruenceSet3 (a : ℕ) : (1 : LocalGL3 v) ∈ converseCongruenceSet3 v a := by
  refine ⟨Subgroup.one_mem _, ?_, ?_, ?_⟩
  · rw [Units.val_one, Matrix.one_apply_ne (by decide), map_zero]
    exact zero_le
  · rw [Units.val_one, Matrix.one_apply_ne (by decide), map_zero]
    exact zero_le
  · rw [Units.val_one, Matrix.one_apply_ne (by decide), map_zero]
    exact zero_le


def IsCongruenceEquivariantAt (a : ℕ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (W : LocalGL3 v → ℂ) : Prop :=
  ∀ k ∈ converseCongruenceSet3 v a, ∀ u : (v.adicCompletion ℚ)ˣ,
    (u : v.adicCompletion ℚ) = (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 →
      ∀ g, W (g * k) = ((χ u : ℂˣ) : ℂ) * W g

def HasVanishingUnipotentIntegralAt (W : LocalGL3 v → ℂ) : Prop :=
  letI := LanglandsTunnell.TateLocal.localBorel ℚ v
  ∀ g : LocalGL3 v,
    (∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)}, W (g * upperUnipotent3 0 x 0)
      ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) = 0

def HasVanishingUnipotentIntegralAlong (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  letI := LanglandsTunnell.TateLocal.localBorel ℚ v
  ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)},
        W (g * localToAdelic3 v (upperUnipotent3 0 x 0))
      ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) = 0


end LocalThree

section Global


def AutomorphyDatum31.zero (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (a : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ) :
    AutomorphyDatum31 pins ψ S a ω 0 lam1 lam2 where
  form := 0
  continuous := continuous_const
  automorphic := fun _ _ => rfl
  central := fun _ _ => by simp
  moderateGrowth := isModerateGrowth3_zero ℚ
  equivariant := fun _ _ _ _ _ _ _ => by simp
  whittaker_eq := fun _ _ => by simp only [whittaker3, Pi.zero_apply, zero_mul, MeasureTheory.integral_zero]
  cuspidalP21 := fun _ _ => by simp
  heckeInvariant := fun _ _ _ _ _ => rfl
  hecke1 := fun p _ => isCosetEigenfunction_zero _ _ (lam1 p)
  hecke2 := fun p _ => isCosetEigenfunction_zero _ _ (lam2 p)

end Global

end LanglandsTunnell.CubicInduction

end

#check @LanglandsTunnell.CubicInduction.localToAdelic3
#check @LanglandsTunnell.CubicInduction.converseCongruenceSet3
#check @LanglandsTunnell.CubicInduction.IsCongruenceEquivariantAt
#check @LanglandsTunnell.CubicInduction.HasVanishingUnipotentIntegralAt
#check @LanglandsTunnell.CubicInduction.AutomorphyDatum31
#check @LanglandsTunnell.CubicInduction.HasVanishingUnipotentIntegralAlong
#check @LanglandsTunnell.CubicInduction.IsCongruenceEquivariantAlong
#print axioms LanglandsTunnell.CubicInduction.localToAdelicN
#print axioms LanglandsTunnell.CubicInduction.one_mem_converseCongruenceSet3
#print axioms LanglandsTunnell.CubicInduction.AutomorphyDatum31.zero
