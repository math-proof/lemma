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
import Abbrev.v1.Atlas.TensorCategories.code.StarAlgebra
set_option maxHeartbeats 800000

open Finset Complex

attribute [instance] StarAlgWithTrace.instRing StarAlgWithTrace.instAlgebra
  StarAlgWithTrace.instStarRing StarAlgWithTrace.instStarModule


namespace StarAlgWithTrace

variable (B : StarAlgWithTrace)

/-- A finite-dimensional ℂ-algebra is Artinian as a ring. -/
instance [FiniteDimensional ℂ B.carrier] : IsArtinianRing B.carrier :=
  isArtinian_of_tower ℂ inferInstance

end StarAlgWithTrace
