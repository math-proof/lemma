/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedHilbertSyzygy.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

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
public import Theorem.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part8
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

public noncomputable section

structure mgsyz_Stage (K : Type u) [Field K] (n : ℕ) where
  W : Type u
  [addCommGroup : AddCommGroup W]
  [moduleR : Module (MvPolynomial (Fin n) K) W]
  [moduleK : Module K W]
  gW : MultigradedPolynomialModule K n W
  N : Submodule (MvPolynomial (Fin n) K) W
  graded :
    letI : DirectSum.Decomposition gW.component := gW.decomposition
    ∀ x ∈ N, ∀ β,
      (((DirectSum.decompose gW.component x) β : gW.component β) : W) ∈ N
  fg : N.FG

end
end MetaMathlibExt
