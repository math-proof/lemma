import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Algebra.Polynomial.RealRooted
open scoped ComplexOrder


namespace MathlibExtTest.Algebra.Polynomial.RealRooted

/--
[linearPolynomial_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
private lemma linearPolynomial_monic (a : ℝ) : (linearPolynomial a).Monic :=
  Polynomial.monic_X_sub_C _

end MathlibExtTest.Algebra.Polynomial.RealRooted

namespace MathlibExtTest.Algebra.Polynomial.RealRooted

/--
[linearPolynomial_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
private lemma linearPolynomial_natDegree (a : ℝ) :
  (linearPolynomial a).natDegree = 1 :=
  Polynomial.natDegree_X_sub_C _

end MathlibExtTest.Algebra.Polynomial.RealRooted

namespace MathlibExtTest.Algebra.Polynomial.RealRooted

/--
[linearPolynomial_realRooted](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
private lemma linearPolynomial_realRooted (a : ℝ) :
  (linearPolynomial a).IsRealRooted := by
  intro z hz
  rw [linearPolynomial, Polynomial.roots_X_sub_C] at hz
  have hz' : z = (a : ℂ) := by simpa using hz
  rw [hz']
  simp

end MathlibExtTest.Algebra.Polynomial.RealRooted

namespace MathlibExtTest.Algebra.Polynomial.RealRooted

/--
[linearPolynomial_maxRealRoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/RealRooted.lean)
-/
@[path]
private lemma linearPolynomial_maxRealRoot (a : ℝ) :
  (linearPolynomial a).maxRealRoot = a := by
  rw [linearPolynomial, Polynomial.maxRealRoot, Polynomial.roots_X_sub_C]
  simp

end MathlibExtTest.Algebra.Polynomial.RealRooted


-- created on 2026-10-23
