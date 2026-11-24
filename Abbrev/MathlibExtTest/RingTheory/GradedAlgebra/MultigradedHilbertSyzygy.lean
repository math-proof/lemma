module
public import Theorem.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part21
public import Theorem.Int.GradedAlgebra.MultigradedHilbertSyzygy
open CategoryTheory CategoryTheory.Limits MvPolynomial


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedHilbertSyzygy.lean -/
noncomputable section

namespace MathlibExtTest.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy

abbrev residueK : Type := Rat

abbrev residueR : Type := MvPolynomial (Fin 2) residueK

end MathlibExtTest.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy
end
