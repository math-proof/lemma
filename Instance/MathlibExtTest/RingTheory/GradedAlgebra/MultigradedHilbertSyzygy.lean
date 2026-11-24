module
public import Theorem.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part21
public import Theorem.Int.GradedAlgebra.MultigradedHilbertSyzygy
public import Abbrev.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy
open CategoryTheory CategoryTheory.Limits MvPolynomial


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedHilbertSyzygy.lean -/
noncomputable section

namespace MathlibExtTest.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy

instance residueModule : Module residueR residueK :=
  Module.compHom _
    (MvPolynomial.constantCoeff : residueR →+* residueK)

instance residueFinite : Module.Finite residueR residueK := by
  apply Module.Finite.of_surjective
    (LinearMap.toSpanSingleton residueR residueK 1)
  intro k
  refine ⟨MvPolynomial.C k, ?_⟩
  change MvPolynomial.constantCoeff (MvPolynomial.C k) • (1 : residueK) = k
  simp

end MathlibExtTest.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy
end
