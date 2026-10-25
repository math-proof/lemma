/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedHilbertSyzygy.lean -/


import Theorem.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part21
import Lemma.Int.GradedAlgebra.MultigradedHilbertSyzygy
open CategoryTheory CategoryTheory.Limits MvPolynomial


noncomputable section

namespace MathlibExtTest.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy

abbrev residueK : Type := Rat

abbrev residueR : Type := MvPolynomial (Fin 2) residueK

end MathlibExtTest.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy
end
