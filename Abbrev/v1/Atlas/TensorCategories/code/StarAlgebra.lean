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
public import Structure.v1.Atlas.TensorCategories.code.StarAlgebra
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


/-- Definition 1.43.1: A `*`-algebra is an associative algebra `B` over `ℂ` with an antilinear
anti-involution and a trace functional whose Hermitian form is positive definite. -/
abbrev Definition_1_43_1 := StarAlgWithTrace

