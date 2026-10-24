import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.EllipticRegularityVar
open TemperedDistribution MvPolynomial DifferentialOperators
open scoped SchwartzMap


namespace DifferentialOperators

/--
[ellipticParametrix_isParametrix](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/EllipticRegularityVar.lean)
-/
@[path]
lemma ellipticParametrix_isParametrix
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
-- given
  (hP : IsElliptic n m P) :
-- imply
  IsParametrix P (ellipticParametrix m P hP) :=
-- proof
  (parametrix_exists_with_singSupp hP).choose_spec.1

end DifferentialOperators

namespace DifferentialOperators

/--
[ellipticParametrix_singularSupport](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/EllipticRegularityVar.lean)
-/
@[path]
lemma ellipticParametrix_singularSupport
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
-- given
  (hP : IsElliptic n m P) :
-- imply
  singularSupport (ellipticParametrix m P hP) ⊆ {(0 : EuclideanSpace ℝ (Fin n))} :=
-- proof
  (parametrix_exists_with_singSupp hP).choose_spec.2

end DifferentialOperators

namespace DifferentialOperators

/--
[elliptic_isHypoelliptic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/EllipticRegularityVar.lean)
-/
@[path]
lemma elliptic_isHypoelliptic
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
-- given
  (hP : IsElliptic n m P) :
-- imply
  IsHypoelliptic P :=
-- proof
  ⟨ellipticParametrix m P hP,
    ellipticParametrix_isParametrix m P hP,
    ellipticParametrix_singularSupport m P hP⟩
end DifferentialOperators



-- created on 2026-10-23
