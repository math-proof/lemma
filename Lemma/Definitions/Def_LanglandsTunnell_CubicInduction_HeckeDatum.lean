import Lemma.Definitions.Def_LanglandsTunnell_ConverseData
import Lemma.Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Lemma.Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.TateGlobal
open LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Generators

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev LocalGL3 : Type := GL (Fin 3) (v.adicCompletion ℚ)

abbrev varpi : v.adicCompletion ℚ := (uniformizerUnit ℚ v : v.adicCompletion ℚ)

theorem varpi_ne_zero : varpi v ≠ 0 := (uniformizerUnit ℚ v).ne_zero

def heckeGen1 : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![varpi v, 1, 1]) (by
    simp [Matrix.det_diagonal, Fin.prod_univ_three, varpi_ne_zero v])

def heckeGen2 : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![varpi v, varpi v, 1]) (by
    simp [Matrix.det_diagonal, Fin.prod_univ_three, varpi_ne_zero v])

def centralGen : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![varpi v, varpi v, varpi v]) (by
    simp [Matrix.det_diagonal, Fin.prod_univ_three, varpi_ne_zero v])

def cNormQ : ℂ := (Ideal.absNorm v.asIdeal : ℂ)

end Generators

section Eigen

variable {G : Type*} [Group G]

def cosetSum {ι : Type} [Fintype ι] (reps : ι → G) (W : G → ℂ) (g : G) : ℂ :=
  ∑ i, W (g * reps i)

def IsCosetEigenfunction (U : Subgroup G) (gen : G) (W : G → ℂ) (lam : ℂ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (reps : ι → G), HeckeIntegralSeam.IsHeckeCosetSystem U gen reps →
    ∀ g : G, cosetSum reps W g = lam * W g

theorem isCosetEigenfunction_zero (U : Subgroup G) (gen : G) (lam : ℂ) :
    IsCosetEigenfunction U gen (fun _ => (0 : ℂ)) lam := by
  intro ι _ reps _ g
  simp [cosetSum]

def IsRightInvariant (U : Subgroup G) (W : G → ℂ) : Prop :=
  ∀ g : G, ∀ u ∈ U, W (g * u) = W g

end Eigen

section Datum

variable {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

def IsInducedSphericalAt (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ))
    (U : Subgroup (LocalGL3 v)) (W : LocalGL3 v → ℂ) : Prop :=
  IsRightInvariant U W ∧
  IsCosetEigenfunction U (heckeGen1 v) W (cNormQ v * inducedE1 ℚ c v) ∧
  IsCosetEigenfunction U (heckeGen2 v) W (cNormQ v * inducedE2 ℚ c v) ∧
  ∀ g : LocalGL3 v, W (centralGen v * g) = inducedE3 ℚ c v * W g

theorem isInducedSphericalAt_zero (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ))
    (U : Subgroup (LocalGL3 v)) : IsInducedSphericalAt c v U (fun _ => (0 : ℂ)) :=
  ⟨fun _ _ _ => rfl, isCosetEigenfunction_zero _ _ _, isCosetEigenfunction_zero _ _ _,
    fun _ => by simp⟩

end Datum

section BadPlaces

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

def IsRamifiedIn (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  ∃ 𝔓 ∈ primeFibre ℚ K v,
    Ideal.ramificationIdx' v.asIdeal 𝔓.asIdeal ≠ 1

def IsTwistRamifiedAbove (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Prop :=
  ∃ 𝔓 ∈ primeFibre ℚ K v, ¬ IsUnramifiedCharAt μ 𝔓

def IsBadPlace (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  IsRamifiedIn K v ∨ IsTwistRamifiedAbove K μ v

def inducedLevelAt (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ :=
  ∑ᶠ 𝔓 ∈ primeFibre ℚ K v,
    v.asIdeal.inertiaDeg' 𝔓.asIdeal * conductorExponentAt K 𝔓 (localChar μ 𝔓)

end BadPlaces

section UniformizerInverse

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem varpi_inv_not_mem_integers : (varpi v)⁻¹ ∉ v.adicCompletionIntegers ℚ := by
  intro h
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀,
    valued_uniformizerUnit ℚ v] at h
  simp at h
  have h' : WithZero.exp (1 : ℤ) ≤ WithZero.exp (0 : ℤ) := h
  exact absurd (WithZero.exp_le_exp.mp h') (by omega)

end UniformizerInverse

end LanglandsTunnell.CubicInduction

end
