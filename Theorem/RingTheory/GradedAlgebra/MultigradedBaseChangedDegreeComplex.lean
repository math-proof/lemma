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
import Def.RingTheory.GradedAlgebra.MultigradedBaseChangedDegreeComplex
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

/-- Each component of the degree inclusion is injective. Source:
Benjamin Braun and Brian Davis, "Antichain Simplices," Journal of
Integer Sequences 23 (2020), lines 864–867,
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`.

Proves `Wanted` entry `MultigradedFreeResolution.baseChangedDegreeInclusion_injective`. -/
theorem
    MultigradedFreeResolution.baseChangedDegreeInclusion_injective
    (K : Type u) [Field K] (n : Nat) (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : Nat → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (α : Fin n →₀ Int) (i : Nat) :
    Function.Injective ⇑(ModuleCat.Hom.hom
      ((MultigradedFreeResolution.baseChangedDegreeInclusion K n M
        targetGraded resolution ι res α).f i)) :=
  Submodule.injective_subtype _

/-- Each component of the degree inclusion has range exactly the
degree piece `baseChangedDegreePiece`. Source: Benjamin Braun and
Brian Davis, "Antichain Simplices," Journal of Integer Sequences 23
(2020), lines 864–867,
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`.

Proves `Wanted` entry `MultigradedFreeResolution.baseChangedDegreeInclusion_range`. -/
theorem
    MultigradedFreeResolution.baseChangedDegreeInclusion_range
    (K : Type u) [Field K] (n : Nat) (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : Nat → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (α : Fin n →₀ Int) (i : Nat) :
    LinearMap.range (ModuleCat.Hom.hom
      ((MultigradedFreeResolution.baseChangedDegreeInclusion K n M
        targetGraded resolution ι res α).f i)) =
      baseChangedDegreePiece (K := K) (n := n) (M := M)
        targetGraded resolution ι res i α :=
  Submodule.range_subtype _

end MetaMathlibExt
