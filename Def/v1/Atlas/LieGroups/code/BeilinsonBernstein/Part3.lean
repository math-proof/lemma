/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Structure.v1.Atlas.LieGroups.code.BeilinsonBernstein.Part2

@[expose] public section

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
