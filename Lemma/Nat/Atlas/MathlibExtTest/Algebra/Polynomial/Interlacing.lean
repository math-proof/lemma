import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Algebra.Polynomial.Interlacing
open scoped BigOperators ComplexOrder


namespace MathlibExtTest.Algebra.Polynomial.Interlacing

/--
[linearPolynomial_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/Interlacing.lean)
-/
@[path]
private lemma linearPolynomial_monic (a : ℝ) : (linearPolynomial a).Monic :=
  Polynomial.monic_X_sub_C _

end MathlibExtTest.Algebra.Polynomial.Interlacing

namespace MathlibExtTest.Algebra.Polynomial.Interlacing

/--
[linearPolynomial_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/Interlacing.lean)
-/
@[path]
private lemma linearPolynomial_natDegree (a : ℝ) :
  (linearPolynomial a).natDegree = 1 :=
  Polynomial.natDegree_X_sub_C _

end MathlibExtTest.Algebra.Polynomial.Interlacing

namespace MathlibExtTest.Algebra.Polynomial.Interlacing

/--
[linearPolynomial_realRooted](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/Interlacing.lean)
-/
@[path]
private lemma linearPolynomial_realRooted (a : ℝ) :
  (linearPolynomial a).IsRealRooted := by
  intro z hz
  rw [linearPolynomial, Polynomial.roots_X_sub_C] at hz
  have hz' : z = (a : ℂ) := by simpa using hz
  rw [hz']
  simp

end MathlibExtTest.Algebra.Polynomial.Interlacing

namespace MathlibExtTest.Algebra.Polynomial.Interlacing

/--
[linearPolynomial_maxRealRoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/Interlacing.lean)
-/
@[path]
private lemma linearPolynomial_maxRealRoot (a : ℝ) :
  (linearPolynomial a).maxRealRoot = a := by
  rw [linearPolynomial, Polynomial.maxRealRoot, Polynomial.roots_X_sub_C]
  simp

end MathlibExtTest.Algebra.Polynomial.Interlacing

namespace MathlibExtTest.Algebra.Polynomial.Interlacing

/--
[weightedSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/Interlacing.lean)
-/
@[path]
private lemma weightedSum_eq :
  ∑ i, (weights i : ℂ) • family i = linearPolynomial (3 / 2) := by
  ext n
  by_cases hzero : n = 0
  · subst n
    norm_num [weights, family, linearPolynomial, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_one]
  · by_cases hone : n = 1
    · subst n
      norm_num [weights, family, linearPolynomial, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_one]
    · simp [weights, family, linearPolynomial, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_one, hzero, Ne.symm hone]

end MathlibExtTest.Algebra.Polynomial.Interlacing

namespace MathlibExtTest.Algebra.Polynomial.Interlacing

/--
[linearCombination_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/Interlacing.lean)
-/
@[path]
private lemma linearCombination_eq (a b t : ℝ) :
  (1 - (t : ℂ)) • linearPolynomial a + (t : ℂ) • linearPolynomial b =
    linearPolynomial ((1 - t) * a + t * b) := by
  simp [linearPolynomial, Polynomial.smul_eq_C_mul]
  ring

end MathlibExtTest.Algebra.Polynomial.Interlacing

namespace MathlibExtTest.Algebra.Polynomial.Interlacing

/--
[family_upperInterlacing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/Interlacing.lean)
-/
@[path]
private lemma family_upperInterlacing (i : Fin 2) :
  (family i).HasUpperInterlacingPoint 0 := by
  fin_cases i
  · change (linearPolynomial 1).HasUpperInterlacingPoint 0
    constructor
    · rw [linearPolynomial_maxRealRoot]
      norm_num
    · intro z hz
      rw [linearPolynomial_maxRealRoot] at hz
      rw [linearPolynomial, Polynomial.roots_X_sub_C] at hz
      simp at hz
  · change (linearPolynomial 2).HasUpperInterlacingPoint 0
    constructor
    · rw [linearPolynomial_maxRealRoot]
      norm_num
    · intro z hz
      rw [linearPolynomial_maxRealRoot] at hz
      rw [linearPolynomial, Polynomial.roots_X_sub_C] at hz
      simp at hz

end MathlibExtTest.Algebra.Polynomial.Interlacing


-- created on 2026-10-23
