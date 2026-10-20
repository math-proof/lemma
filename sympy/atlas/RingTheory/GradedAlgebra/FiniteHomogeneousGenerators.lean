/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/FiniteHomogeneousGenerators.lean -/

import sympy.atlas.RingTheory.GradedAlgebra.MultigradedPolynomialModule
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite homogeneous generators for multigraded polynomial modules

Every finite module over the standard multigraded polynomial ring admits a
finite generating set consisting of homogeneous elements.

Source: Braun-Davis, JIS 23 (2020), span 856-877.
See https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex
-/

namespace MetaMathlibExt

/-- Finite generating set of homogeneous elements for a finite multigraded
polynomial module. Source: Braun-Davis, JIS 23 (2020), span 856-877;
see https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex -/
theorem MultigradedPolynomialModule.exists_finset_homogeneous_generators
    (K : Type*) [Field K] (n : ℕ) (M : Type*)
    [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    ∃ s : Finset M,
      (∀ m ∈ s, ∃ α : Fin n →₀ Int, m ∈ targetGraded.component α) ∧
      Submodule.span (MvPolynomial (Fin n) K) (s : Set M) = ⊤ := by
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
      rw [← genIdxEq, recon]
      exact sumInSpan
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
