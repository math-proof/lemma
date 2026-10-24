/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedBaseChangedDifferential.lean -/

import sympy.atlas.RingTheory.GradedAlgebra.MultigradedBetti
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.MvPolynomial.Basic
import sympy.atlas.RingTheory.GradedAlgebra.MultigradedZeroEvalBaseChange
import Lemma.Int.GradedAlgebra.MultigradedZeroEvalBaseChange
namespace MetaMathlibExt

universe u

/-- The scalar-extended differential preserves multidegree: a graded free
resolution splits into degree-indexed complexes, and tensoring along the
augmentation uses the differential `Id tensor partial`, so the `(i + 1) → i`
base-changed differential maps the degree-`α` piece to itself.
Source: Benjamin Braun and Brian Davis, "Antichain Simplices,"
Journal of Integer Sequences 23 (2020), lines 862–867,
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`.

Proves `Wanted` entry `MultigradedFreeResolution.baseChangedDifferential_preservesDegree`.
-/
theorem MultigradedFreeResolution.baseChangedDifferential_preservesDegree
    {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : ℕ → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (i : ℕ) (α : Fin n →₀ Int)
    (x : ↥((baseChangedComplex (K := K) (n := n) (M := M) resolution).X (i + 1)))
    (hx : x ∈ baseChangedDegreePiece (K := K) (n := n) (M := M) targetGraded
      resolution ι res (i + 1) α) :
    (ModuleCat.Hom.hom
      ((baseChangedComplex (K := K) (n := n) (M := M) resolution).d (i + 1)
        i)) x ∈
      baseChangedDegreePiece (K := K) (n := n) (M := M) targetGraded resolution
        ι res i α := by
  let _ : Module K ↥(resolution.complex.X (i + 1)) :=
    Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
  let _ : Module K ↥(resolution.complex.X i) :=
    Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
  let _ : Algebra (MvPolynomial (Fin n) K) K := zeroEval.toAlgebra
  change x ∈ Submodule.span K
    {y | ∃ j : ι (i + 1), (res.termFree (i + 1)).degree j = α ∧
      y = (res.termFree (i + 1)).basis.baseChange K j} at hx
  refine Submodule.span_induction (p := fun y _ =>
    (ModuleCat.Hom.hom
      ((baseChangedComplex resolution).d (i + 1) i)) y ∈
      baseChangedDegreePiece targetGraded resolution ι res i α) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨j, hj, rfl⟩
    rw [Module.Basis.baseChange_apply]
    have hmap :
        (ModuleCat.Hom.hom
          ((baseChangedComplex resolution).d (i + 1) i))
            ((1 : K) ⊗ₜ[MvPolynomial (Fin n) K]
              (res.termFree (i + 1)).basis j :
                TensorProduct (MvPolynomial (Fin n) K) K
                  ↥(resolution.complex.X (i + 1))) =
          ((1 : K) ⊗ₜ[MvPolynomial (Fin n) K]
              (ModuleCat.Hom.hom (resolution.complex.d (i + 1) i))
                ((res.termFree (i + 1)).basis j) :
            TensorProduct (MvPolynomial (Fin n) K) K
              ↥(resolution.complex.X i)) := by
      change (ModuleCat.Hom.hom
        ((ModuleCat.extendScalars zeroEval).map
          (resolution.complex.d (i + 1) i)))
          ((1 : K) ⊗ₜ[MvPolynomial (Fin n) K]
            (res.termFree (i + 1)).basis j) = _
      exact ModuleCat.ExtendScalars.map_tmul zeroEval
        (resolution.complex.d (i + 1) i) (1 : K)
          ((res.termFree (i + 1)).basis j)
    rw [hmap]
    apply (res.termFree i).baseChange_mem_degreeSpan α
    apply res.diffDegreeZero i α
    rw [← hj]
    exact (res.termFree (i + 1)).basis_mem j
  · simp
  · intro y z _ _ hy hz
    rw [map_add]
    exact (baseChangedDegreePiece targetGraded resolution ι res i α).add_mem hy hz
  · intro k y _ hy
    rw [map_smul]
    exact (baseChangedDegreePiece targetGraded resolution ι res i α).smul_mem k hy

end MetaMathlibExt
