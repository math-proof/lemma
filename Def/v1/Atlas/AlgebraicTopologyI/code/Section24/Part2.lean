/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RingTheory.Flat.CategoryTheory
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section24
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
