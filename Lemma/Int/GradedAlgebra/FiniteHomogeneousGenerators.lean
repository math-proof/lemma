import Mathlib
import sympy.Basic
import Structure.RingTheory.GradedAlgebra.MultigradedPolynomialModule


namespace MetaMathlibExt

/--
[MultigradedPolynomialModule.exists_finset_homogeneous_generators](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/FiniteHomogeneousGenerators.lean)
-/
@[path]
lemma MultigradedPolynomialModule.exists_finset_homogeneous_generators
  [Field K] [AddCommGroup M] [Module K M]
  {n : ℕ} [Module (MvPolynomial (Fin n) K) M] [Module.Finite (MvPolynomial (Fin n) K) M]
  {targetGraded : MultigradedPolynomialModule K n M} :
-- imply
  ∃ s : Finset M,
    (∀ m ∈ s, ∃ α : Fin n →₀ Int, m ∈ targetGraded.component α) ∧
    Submodule.span (MvPolynomial (Fin n) K) (s : Set M) = ⊤ := by
-- proof
  classical
  set_option linter.style.haveILetI false in
  letI : DirectSum.Decomposition targetGraded.component :=
    targetGraded.decomposition
  obtain ⟨genCount, genFun, genSpan⟩ := (Module.Finite.exists_fin :
    ∃ (count : ℕ) (gen : Fin count → M),
      Submodule.span (MvPolynomial (Fin n) K) (Set.range gen) = ⊤)
  refine ⟨Finset.univ.biUnion (fun genIdx =>
    (DirectSum.decompose targetGraded.component (genFun genIdx)).support.image
      (fun deg =>
        (((DirectSum.decompose targetGraded.component (genFun genIdx)) deg) : M))),
    ?_, ?_⟩
  · intro homElem homMem
    rw [Finset.mem_biUnion] at homMem
    obtain ⟨genIdx, _, imageMem⟩ := homMem
    rw [Finset.mem_image] at imageMem
    obtain ⟨deg, _, rfl⟩ := imageMem
    exact ⟨deg, ((DirectSum.decompose targetGraded.component (genFun genIdx)) deg).property⟩
  · have rangeSubset :
    Set.range genFun ⊆ ↑(Submodule.span (MvPolynomial (Fin n) K)
      ((Finset.univ.biUnion (fun genIdx =>
        (DirectSum.decompose targetGraded.component (genFun genIdx)).support.image
          (fun deg =>
            (((DirectSum.decompose targetGraded.component (genFun genIdx)) deg) :
              M)))) : Set M)) := by
    intro genElem genRangeMem
    obtain ⟨genIdx, genIdxEq⟩ := genRangeMem
    have recon : genFun genIdx =
      Finset.sum
        (DirectSum.decompose targetGraded.component (genFun genIdx)).support
        (fun deg =>
          (((DirectSum.decompose targetGraded.component (genFun genIdx)) deg) : M)) :=
      (DirectSum.sum_support_decompose targetGraded.component
        (genFun genIdx)).symm
    have sumInSpan :
      Finset.sum
        (DirectSum.decompose targetGraded.component (genFun genIdx)).support
        (fun deg =>
          (((DirectSum.decompose targetGraded.component (genFun genIdx)) deg) : M)) ∈
      Submodule.span (MvPolynomial (Fin n) K)
        ((Finset.univ.biUnion (fun genIdx =>
          (DirectSum.decompose targetGraded.component (genFun genIdx)).support.image
            (fun deg =>
              (((DirectSum.decompose targetGraded.component (genFun genIdx)) deg) :
                M)))) : Set M) := by
      apply Submodule.sum_mem
      intro deg degMem
      apply Submodule.subset_span
      rw [Finset.mem_coe, Finset.mem_biUnion]
      exact ⟨genIdx, Finset.mem_univ genIdx, Finset.mem_image.mpr ⟨deg, degMem, rfl⟩⟩
    rwa [← genIdxEq, recon]
    have spanIneq :
      Submodule.span (MvPolynomial (Fin n) K) (Set.range genFun) ≤
        Submodule.span (MvPolynomial (Fin n) K)
          ((Finset.univ.biUnion (fun genIdx =>
            (DirectSum.decompose targetGraded.component (genFun genIdx)).support.image
              (fun deg =>
                (((DirectSum.decompose targetGraded.component (genFun genIdx)) deg) :
                  M)))) : Set M) :=
      (Submodule.span_le).mpr rangeSubset
    rw [genSpan] at spanIneq
    exact eq_top_iff.mpr spanIneq

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
