/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedHilbertSyzygy.lean -/


import sympy.atlas.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy
import Lemma.Int.GradedAlgebra.MultigradedHilbertSyzygy


open CategoryTheory CategoryTheory.Limits MvPolynomial

noncomputable section

namespace MathlibExtTest.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy

abbrev residueK : Type := Rat
abbrev residueR : Type := MvPolynomial (Fin 2) residueK

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
