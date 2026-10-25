/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Structure.v1.Atlas.LieGroups.code.BeilinsonBernstein.Part2
open CategoryTheory


namespace BeilinsonBernstein

noncomputable section

universe u

attribute [instance] CAlgebra.instRing CAlgebra.instAlgebra

attribute [instance] AbCat.instCat

attribute [instance] GradedAlgebra.instRing GradedAlgebra.instAlgebra

attribute [instance] BBDataZero.instLieRing BBDataZero.instLieAlgebra BBDataZero.instSemisimple

noncomputable def BBDataZero.a₀ (D : BBDataZero) : D.U₀.carrier →ₐ[ℂ] D.DF.carrier :=
  AlgHom.liftOfSurjectiveNC D.proj₀ D.proj₀_surjective D.actionMap D.ker_inclusion

end
end BeilinsonBernstein
