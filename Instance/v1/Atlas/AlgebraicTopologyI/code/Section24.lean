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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section24
open CategoryTheory MonoidalCategory Limits


noncomputable section

namespace UniversalCoefficientTheorem

/-- Tensoring on the right with a fixed module $M$ preserves colimits; obtained by
transporting along the symmetry isomorphism with `tensorLeft M`. -/
instance tensorRight_preservesColimits (R : Type*) [CommRing R] (M : ModuleCat R) :
    PreservesColimits ((tensoringRight (ModuleCat R)).obj M) := by
  change PreservesColimits (tensorRight M)
  exact preservesColimits_of_natIso
    (NatIso.ofComponents (fun X => (_root_.CategoryTheory.BraidedCategory.braiding M X))
      (fun {X Y} f => _root_.CategoryTheory.BraidedCategory.braiding_naturality_right M f) :
      tensorLeft M ≅ tensorRight M)

end UniversalCoefficientTheorem
end
