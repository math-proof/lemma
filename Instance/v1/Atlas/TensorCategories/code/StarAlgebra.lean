module
public import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
public import Theorem.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
public import Theorem.Category.Atlas.v1.TensorCategories.code.BasedRings
public import Abbrev.v1.Atlas.TensorCategories.code.BasedRings
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Star.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Abbrev.v1.Atlas.TensorCategories.code.StarAlgebra
set_option maxHeartbeats 800000
open Finset Complex


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

attribute [instance] StarAlgWithTrace.instRing StarAlgWithTrace.instAlgebra
  StarAlgWithTrace.instStarRing StarAlgWithTrace.instStarModule


namespace StarAlgWithTrace

variable (B : StarAlgWithTrace)

/-- A finite-dimensional ℂ-algebra is Artinian as a ring. -/
instance [FiniteDimensional ℂ B.carrier] : IsArtinianRing B.carrier :=
  isArtinian_of_tower ℂ inferInstance

end StarAlgWithTrace
