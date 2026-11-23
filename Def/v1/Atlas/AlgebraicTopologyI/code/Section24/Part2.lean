/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section24

@[expose] public section

open CategoryTheory MonoidalCategory Limits


noncomputable section

namespace UniversalCoefficientTheorem

/-- The map $Z_{n+1}(C) \otimes M \to H_{n+1}(C \otimes M)$ obtained by lifting through
the cycles of the tensor complex and then quotienting by boundaries. This is the building
block of the UCT map $\alpha$. -/
def cyclesToHomologyTC (R : Type*) [CommRing R] (M : ModuleCat R)
    (n : ℕ) (C : ChainComplex (ModuleCat R) ℕ) :
    ((tensoringRight (ModuleCat R)).obj M).obj (C.cycles (n + 1)) ⟶
      (tensorComplex R C M).homology (n + 1) :=
  (tensorComplex R C M).liftCycles
    (((tensoringRight (ModuleCat R)).obj M).map (C.iCycles (n + 1)))
    n (down_next_succ n) (iCycles_tensor_comp_d R M n C) ≫
  (tensorComplex R C M).homologyπ (n + 1)

end UniversalCoefficientTheorem
end
