/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/NormalizedPlace.lean -/


import Def.NumberTheory.NumberField.NormalizedPlace
import Lemma.Nat.NumberField.NormalizedPlace
open NumberField


namespace MathlibExtTest.NumberTheory.NormalizedPlace

variable {R : Type*} [Semiring R]

variable {K : Type*} [Field K] [NumberField K]

example (v : AbsoluteValue R ℝ) : v.rpow 1 zero_lt_one le_rfl = v := by
  ext x
  simp

example (v : AbsoluteValue R ℝ) (c : ℝ) (hc₀ : 0 < c) (hc₁ : c ≤ 1) (x y : R) :
    v.rpow c hc₀ hc₁ (x * y) = v.rpow c hc₀ hc₁ x * v.rpow c hc₀ hc₁ y := by
  exact map_mul (v.rpow c hc₀ hc₁) x y

example (v : FinitePlace K) (x : K) :
    v.normalizedAbsoluteValue x =
      (HeightOneSpectrum.adicAbv K v.maximalIdeal x) ^
        (1 / (Module.finrank ℚ K : ℝ)) := by
  exact v.normalizedAbsoluteValue_apply_eq_adicAbv x

example (v : InfinitePlace K) (hv : v.IsReal) (x : K) :
    v.normalizedAbsoluteValue x = v x ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  exact v.normalizedAbsoluteValue_apply_of_isReal hv x

example (v : InfinitePlace K) (hv : v.IsComplex) (x : K) :
    v.normalizedAbsoluteValue x = v x ^ (2 / (Module.finrank ℚ K : ℝ)) := by
  exact v.normalizedAbsoluteValue_apply_of_isComplex hv x

example (x : ℚ) : Rat.infinitePlace.normalizedAbsoluteValue x = |x| := by
  rw [Rat.infinitePlace.normalizedAbsoluteValue_apply_of_isReal Rat.isReal_infinitePlace]
  norm_num

end MathlibExtTest.NumberTheory.NormalizedPlace
