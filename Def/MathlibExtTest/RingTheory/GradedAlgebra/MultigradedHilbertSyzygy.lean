/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedHilbertSyzygy.lean -/


import Theorem.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part21
import Lemma.Int.GradedAlgebra.MultigradedHilbertSyzygy
import Instance.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy
open CategoryTheory CategoryTheory.Limits MvPolynomial


noncomputable section

namespace MathlibExtTest.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy

def residueComponent (α : Fin 2 →₀ ℤ) : Submodule residueK residueK :=
  if α = 0 then ⊤ else ⊥

@[instance_reducible]
def residueDecomposition : DirectSum.Decomposition residueComponent := by
  classical
  apply DirectSum.IsInternal.chooseDecomposition _
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro α
    by_cases hα : α = 0 <;> simp [residueComponent, hα]
  · apply le_antisymm le_top
    have h := le_iSup (fun α => residueComponent α) (0 : Fin 2 →₀ ℤ)
    rwa [show residueComponent 0 = ⊤ by simp [residueComponent]] at h

def residueGrading :
    MetaMathlibExt.MultigradedPolynomialModule residueK 2 residueK where
  component := residueComponent
  decomposition := residueDecomposition
  smul_via_C := by
    intro k m
    change k • m = MvPolynomial.constantCoeff (MvPolynomial.C k) • m
    simp
  monomial_mem := by
    intro a c α m hm
    by_cases ha : a = 0
    · subst a
      have hsmul := (residueComponent α).smul_mem c hm
      change MvPolynomial.constantCoeff (MvPolynomial.monomial 0 c) • m ∈
        residueComponent (α + MetaMathlibExt.natDegreeToInt 0)
      simpa [MetaMathlibExt.natDegreeToInt] using hsmul
    · change MvPolynomial.constantCoeff (MvPolynomial.monomial a c) • m ∈ _
      rw [MvPolynomial.constantCoeff_monomial]
      simp [ha]

end MathlibExtTest.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy
end
