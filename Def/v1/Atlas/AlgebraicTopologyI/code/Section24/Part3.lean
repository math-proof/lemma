module
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section24.Part2
open CategoryTheory MonoidalCategory Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace UniversalCoefficientTheorem

/-- The UCT map $\alpha : H_{n+1}(C) \otimes M \to H_{n+1}(C \otimes M)$, defined by
descending the cycles-to-homology map through the cokernel presentation of $H_{n+1}(C)$
(valid because tensoring with $M$ preserves the relevant cokernel for free $C$). -/
def uctAlpha (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ)
    (C : ChainComplex (ModuleCat R) ℕ) (_hfree : ∀ i, Module.Free R (C.X i)) :
    C.homology (n + 1) ⊗ M ⟶ (tensorComplex R C M).homology (n + 1) := by
  have hcokerF := isColimitCoforkMapOfIsColimit'
    ((tensoringRight (ModuleCat R)).obj M)
    (C.toCycles_comp_homologyπ (n + 2) (n + 1))
    (C.homologyIsCokernel (n + 2) (n + 1) (down_prev_succ n))
  exact (Cofork.IsColimit.desc' hcokerF
    (cyclesToHomologyTC R M n C)
    (by rw [toCycles_comp_cyclesToHomologyTC, zero_comp])).1

end UniversalCoefficientTheorem
end
