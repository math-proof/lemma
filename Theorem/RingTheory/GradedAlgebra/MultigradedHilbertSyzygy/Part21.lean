module
public import Structure.RingTheory.GradedAlgebra.MultigradedFreeResolution
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Theorem.Int.GradedAlgebra.FiniteHomogeneousGenerators
public import Def.RingTheory.Polynomial.HilbertSyzygy
public import Theorem.Int.Polynomial.HilbertSyzygy
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Def.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part19


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedHilbertSyzygy.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Finite multigraded free resolutions over polynomial rings

Existence of a finite multigraded free resolution with finite homogeneous
basis types for every finitely generated module carrying the campaign
multigrading over `MvPolynomial (Fin n) K`.

Direct source for the existence claim: Hoffman–Wang,
*Regularity and Resolutions for Multigraded Modules*,
https://export.arxiv.org/e-print/math/0601101v1 lines 592-612, which states
that any finitely generated multigraded module has a finite free graded
resolution by finite direct sums of shifted copies of the polynomial algebra.

Motivation and multigraded Betti / Poincaré-series context: Braun–Davis,
*Antichain Simplices*, Journal of Integer Sequences 23 (2020),
https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex lines 856-876,
which records the Hilbert Syzygy consequence that the Poincaré series is a
polynomial over a polynomial ring. That JIS passage motivates this edge but
is not its proof source.

This edge claims finite termination only: no numerical bound `≤ n`, no
minimality or uniqueness, no base change, and no Poincaré-series conclusion.
-/
namespace MetaMathlibExt

universe u

open CategoryTheory MvPolynomial

noncomputable section

attribute [local instance] mgsyz_Stage.addCommGroup mgsyz_Stage.moduleR
  mgsyz_Stage.moduleK

/-- Existence of a finite multigraded free resolution over `MvPolynomial`.

Direct source: Hoffman–Wang,
https://export.arxiv.org/e-print/math/0601101v1 lines 592-612 (finite free
graded resolution). The Braun–Davis JIS passage
https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex lines 856-876
supplies the motivating Hilbert-syzygy / Poincaré-series context only. No
`≤ n` bound is claimed here.

Proves `Wanted` entry `exists_finite_multigraded_free_resolution`.

Proof: Uses stagewise minimal homogeneous free covers, the determinant trick,
dimension shifting, and Hilbert's syzygy theorem.
-/
theorem exists_finite_multigraded_free_resolution
    (K : Type u) (n : ℕ) (M : Type u)
    [Field K] [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    ∃ (resolution : CategoryTheory.ProjectiveResolution
        (ModuleCat.of (MvPolynomial (Fin n) K) M))
      (ι : ℕ → Type u)
      (res : MultigradedFreeResolution K n M targetGraded resolution ι)
      (bound : ℕ),
      (∀ i, Finite (ι i)) ∧ ∀ i, bound < i → IsEmpty (ι i) := by
  refine ⟨mgsyz_resolution K n M targetGraded,
    mgsyz_ιk K n M targetGraded,
    mgsyz_multigradedResolution K n M targetGraded, n, ?_, ?_⟩
  · intro i
    infer_instance
  · intro i hi
    exact mgsyz_ιk_isEmpty_of_lt K n M targetGraded i hi

end
end MetaMathlibExt
