/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/Interlacing.lean -/

import Def.Algebra.Polynomial.Interlacing
import Lemma.Polynomial.Interlacing
open scoped BigOperators ComplexOrder


namespace MathlibExtTest.Algebra.Polynomial.Interlacing

noncomputable section

def linearPolynomial (a : ℝ) : Polynomial ℂ :=
  Polynomial.X - Polynomial.C (a : ℂ)

def weights : Fin 2 → ℝ := ![1 / 2, 1 / 2]

def family : Fin 2 → Polynomial ℂ :=
  ![linearPolynomial 1, linearPolynomial 2]

end
end MathlibExtTest.Algebra.Polynomial.Interlacing
