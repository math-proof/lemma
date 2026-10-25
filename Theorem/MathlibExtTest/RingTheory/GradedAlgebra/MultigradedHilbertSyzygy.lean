/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedHilbertSyzygy.lean -/


import Theorem.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part21
import Lemma.Int.GradedAlgebra.MultigradedHilbertSyzygy
import Def.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy
open CategoryTheory CategoryTheory.Limits MvPolynomial


noncomputable section

namespace MathlibExtTest.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy

-- The two-variable residue field has a projective resolution with eventually zero terms.
example :
    ∃ (resolution : ProjectiveResolution (ModuleCat.of residueR residueK))
      (bound : ℕ), ∀ i, bound < i → IsZero (resolution.complex.X i) := by
  obtain ⟨resolution, ι, res, bound, _, hempty⟩ :=
    MetaMathlibExt.exists_finite_multigraded_free_resolution
      residueK 2 residueK residueGrading
  refine ⟨resolution, bound, ?_⟩
  intro i hi
  let : IsEmpty (ι i) := hempty i hi
  let : Module residueK ↥(resolution.complex.X i) :=
    Module.compHom _ (MvPolynomial.C : residueK →+* residueR)
  let : Subsingleton ↥(resolution.complex.X i) :=
    ⟨by
      intro x y
      apply (res.termFree i).basis.repr.injective
      ext j
      exact isEmptyElim j⟩
  exact ModuleCat.isZero_of_subsingleton _

end MathlibExtTest.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy
end
