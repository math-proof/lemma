import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Algebra.MvPolynomial.Stable
open MvPolynomial MathlibExtTest MathlibExtTest.Algebra MathlibExtTest.Algebra.MvPolynomial MathlibExtTest.Algebra.MvPolynomial.Stable
open scoped ComplexOrder


namespace MathlibExtTest.Algebra.MvPolynomial.Stable

/--
[unitX_isStable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/MvPolynomial/Stable.lean)
-/
@[path]
lemma unitX_isStable
-- imply
  (X () : MvPolynomial Unit ℂ).IsStable := by
-- proof
  intro z hz hzero
  have him := hz ()
  simp only [eval_X] at hzero
  rw [hzero] at him
  norm_num at him

end MathlibExtTest.Algebra.MvPolynomial.Stable

namespace MathlibExtTest.Algebra.MvPolynomial.Stable

/--
[unitX_isRealStable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/MvPolynomial/Stable.lean)
-/
@[path]
private lemma unitX_isRealStable : (X () : MvPolynomial Unit ℂ).IsRealStable :=
⟨by simp, unitX_isStable⟩

end MathlibExtTest.Algebra.MvPolynomial.Stable


-- created on 2026-10-23
