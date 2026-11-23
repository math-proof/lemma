/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/RealRooted.lean -/

module

public import Def.Algebra.Polynomial.RealRooted.Part2
public import Theorem.Polynomial.RealRooted

@[expose] public section

open scoped ComplexOrder


namespace MathlibExtTest.Algebra.Polynomial.RealRooted

noncomputable section

/-- A linear polynomial used to exercise the real-rooted API. -/
def linearPolynomial (a : ℝ) : Polynomial ℂ :=
  Polynomial.X - Polynomial.C (a : ℂ)

end
end MathlibExtTest.Algebra.Polynomial.RealRooted
