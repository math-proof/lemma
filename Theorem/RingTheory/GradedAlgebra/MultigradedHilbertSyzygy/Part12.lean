/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedHilbertSyzygy.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Structure.RingTheory.GradedAlgebra.MultigradedFreeResolution
import Mathlib.LinearAlgebra.Dimension.Finite
import Lemma.Int.GradedAlgebra.FiniteHomogeneousGenerators
import Def.RingTheory.Polynomial.HilbertSyzygy
import Lemma.Int.Polynomial.HilbertSyzygy
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import Def.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part9
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

section mgsyz_MinimalCover

theorem mgsyz_cover_spec (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) :
    (mgsyz_cover (K := K) n S).card = mgsyz_minCard (K := K) n S ∧
      (∀ m ∈ mgsyz_cover (K := K) n S,
        ∃ α : Fin n →₀ ℤ, m ∈ S.gW.component α) ∧
      Submodule.span (MvPolynomial (Fin n) K)
        (mgsyz_cover (K := K) n S : Set S.W) = S.N := by
  classical
  exact Classical.choose_spec (mgsyz_minCard_spec (K := K) n S)

theorem mgsyz_cover_card (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) :
    (mgsyz_cover (K := K) n S).card = mgsyz_minCard (K := K) n S :=
  (mgsyz_cover_spec (K := K) n S).1

theorem mgsyz_cover_homogeneous (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) (m : S.W)
    (hm : m ∈ mgsyz_cover (K := K) n S) :
    ∃ α : Fin n →₀ ℤ, m ∈ S.gW.component α :=
  (mgsyz_cover_spec (K := K) n S).2.1 m hm

theorem mgsyz_cover_span (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) :
    Submodule.span (MvPolynomial (Fin n) K)
      (mgsyz_cover (K := K) n S : Set S.W) = S.N :=
  (mgsyz_cover_spec (K := K) n S).2.2

end mgsyz_MinimalCover
end
end MetaMathlibExt
