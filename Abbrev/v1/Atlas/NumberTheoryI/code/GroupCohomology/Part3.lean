/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Structure.v1.Atlas.NumberTheoryI.code.GroupCohomology.Part3


noncomputable section

open CategoryTheory

universe u

namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

attribute [instance] FreeResolution.free

attribute [instance] IsAdditiveCategory.hasFiniteBiproducts

section ExactFunctor

open CategoryTheory.Limits CategoryTheory.ShortComplex

variable {C' : Type*} [Category C'] [Limits.HasZeroMorphisms C']

abbrev IsLeftExactFunctor {C' D' : Type*} [Category C'] [Category D']
    (F : C' ⥤ D') : Prop :=
  PreservesFiniteLimits F

abbrev IsRightExactFunctor {C' D' : Type*} [Category C'] [Category D']
    (F : C' ⥤ D') : Prop :=
  PreservesFiniteColimits F

abbrev LeftExact (C' D' : Type*) [Category C'] [Category D'] :=
  LeftExactFunctor C' D'

abbrev RightExact (C' D' : Type*) [Category C'] [Category D'] :=
  RightExactFunctor C' D'

end ExactFunctor

end GroupCohomology

namespace ChainComplexDef

open CategoryTheory

universe v

variable {R : Type v} [Ring R]

abbrev ChainComplexRMod (R : Type v) [Ring R] := ChainComplex (ModuleCat.{v} R) ℕ

abbrev chainObject (C : ChainComplexRMod R) (n : ℕ) : ModuleCat R := C.X n

abbrev boundaryMap (C : ChainComplexRMod R) (n : ℕ) :
    chainObject C (n + 1) ⟶ chainObject C n :=
  C.d (n + 1) n

abbrev chainHomology (C : ChainComplexRMod R) (n : ℕ) : ModuleCat R := C.homology n

end ChainComplexDef
end
