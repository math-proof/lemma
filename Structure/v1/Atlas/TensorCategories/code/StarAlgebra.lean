/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Lemma.Category.Atlas.v1.TensorCategories.code.BasedRings
import Abbrev.v1.Atlas.TensorCategories.code.BasedRings
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option maxHeartbeats 800000

open Finset Complex


/-- A `*`-algebra with trace: an associative ℂ-algebra with a star structure, a linear trace
satisfying `τ(ab) = τ(ba)`, and a positive definiteness condition `0 < Re τ(a * star a)` for
`a ≠ 0`. -/
structure StarAlgWithTrace where
  carrier : Type*
  [instRing : Ring carrier]
  [instAlgebra : Algebra ℂ carrier]
  [instStarRing : StarRing carrier]
  [instStarModule : StarModule ℂ carrier]
  trace : carrier →ₗ[ℂ] ℂ
  trace_comm : ∀ a b, trace (a * b) = trace (b * a)
  trace_pos_def : ∀ a, a ≠ 0 → 0 < (trace (a * star a)).re

