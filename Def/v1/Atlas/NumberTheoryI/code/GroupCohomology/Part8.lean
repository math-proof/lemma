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
import Abbrev.v1.Atlas.NumberTheoryI.code.GroupCohomology.Part5


noncomputable section

open CategoryTheory

universe u

namespace ChainHomotopy

open CategoryTheory

universe v

variable {R : Type v} [Ring R]

def cochainCohomologyFunctor (R : Type v) [Ring R] (n : ℕ) :
    CochainComplexRMod R ⥤ ModuleCat R :=
  HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℕ) n

end DerivedFunctor

namespace LongExactDerived

open CategoryTheory

universe v

variable {R : Type v} [Ring R]

def cochainConnectingHomomorphism
    {S : ShortComplex (DerivedFunctor.CochainComplexRMod R)}
    (hS : S.ShortExact) (n : ℕ) :
    DerivedFunctor.cochainCohomology S.X₃ n ⟶ DerivedFunctor.cochainCohomology S.X₁ (n + 1) :=
  hS.δ n (n + 1) rfl

end LongExactDerived
end
