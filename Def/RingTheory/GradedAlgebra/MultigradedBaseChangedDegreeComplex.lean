/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedBaseChangedDegreeComplex.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Def.RingTheory.GradedAlgebra.MultigradedBetti.Part2
import Theorem.RingTheory.GradedAlgebra.MultigradedBaseChangedDifferential
import Lemma.Int.GradedAlgebra.MultigradedBaseChangedDifferential
import Def.RingTheory.GradedAlgebra.MultigradedBaseChangedTermDecomposition
import Lemma.Int.GradedAlgebra.MultigradedBaseChangedDegreePieceFinite
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic
/-!
# Degree components of the base-changed multigraded resolution

This file provides the degree-`α` complex of the base-changed multigraded
free resolution, its inclusion into the base-changed complex, the
inclusion's componentwise injectivity and range, and the assembly of the
repository's `MultigradedBaseChange` package from these pieces.

Source: Benjamin Braun and Brian Davis, "Antichain Simplices,"
Journal of Integer Sequences 23 (2020), lines 864–867,
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`.
-/


namespace MetaMathlibExt

universe u

/-- Degree-`α` complex of the base-changed resolution: the complex of
`K`-vector spaces assembled from the degree-`α` pieces. Source:
Benjamin Braun and Brian Davis, "Antichain Simplices," Journal of
Integer Sequences 23 (2020), lines 864–867,
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`.

Proves `Wanted` entry `MultigradedFreeResolution.baseChangedDegreeComplex`. -/
noncomputable def MultigradedFreeResolution.baseChangedDegreeComplex
    (K : Type u) [Field K] (n : Nat) (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : Nat → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (α : Fin n →₀ Int) :
    HomologicalComplex (ModuleCat.{u} K) (ComplexShape.down Nat) :=
  ChainComplex.of
    (fun i => ModuleCat.of K
      ↥(baseChangedDegreePiece (K := K) (n := n) (M := M) targetGraded
        resolution ι res i α))
    (fun i => ModuleCat.ofHom (LinearMap.restrict
      (ModuleCat.Hom.hom ((baseChangedComplex resolution).d (i + 1) i))
      (fun x hx =>
        MultigradedFreeResolution.baseChangedDifferential_preservesDegree
          targetGraded resolution ι res i α x hx)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hbase := (baseChangedComplex resolution).d_comp_d (n + 1 + 1) (n + 1) n
      have hhom : ((baseChangedComplex resolution).d (n + 1) n).hom.comp
          ((baseChangedComplex resolution).d (n + 1 + 1) (n + 1)).hom = 0 := by
        rw [← ModuleCat.hom_comp, hbase, ModuleCat.hom_zero]
      have happ := LinearMap.congr_fun hhom ↑x
      simpa using happ)

/-- Inclusion of the degree-`α` complex into the base-changed complex.
Source: Benjamin Braun and Brian Davis, "Antichain Simplices,"
Journal of Integer Sequences 23 (2020), lines 864–867,
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`.

Proves `Wanted` entry `MultigradedFreeResolution.baseChangedDegreeInclusion`. -/
noncomputable def MultigradedFreeResolution.baseChangedDegreeInclusion
    (K : Type u) [Field K] (n : Nat) (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : Nat → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (α : Fin n →₀ Int) :
    HomologicalComplex.Hom
      (MultigradedFreeResolution.baseChangedDegreeComplex K n M
        targetGraded resolution ι res α)
      (baseChangedComplex (K := K) (n := n) (M := M) resolution) :=
  ChainComplex.ofHom
    (fun i => by
      letI := ModuleCat.isAddCommGroup ((baseChangedComplex resolution).X i)
      letI := ModuleCat.isModule ((baseChangedComplex resolution).X i)
      exact (ModuleCat.ofHom (Submodule.subtype
        (baseChangedDegreePiece (K := K) (n := n) (M := M) targetGraded
          resolution ι res i α)) :
        ModuleCat.of K
          ↥(baseChangedDegreePiece (K := K) (n := n) (M := M) targetGraded
            resolution ι res i α) ⟶
          ModuleCat.of K ↥((baseChangedComplex resolution).X i)))
    (fun i => by
      simp only [MultigradedFreeResolution.baseChangedDegreeComplex,
        ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp)

end MetaMathlibExt
