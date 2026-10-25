/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneReal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneNat.Part4
import Mathlib.Data.Finset.Sort
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneReal
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def realValueSet (f : ConfigSpace E -> ℝ) : Finset ℝ :=
  Finset.univ.image f


noncomputable def realLevels (f : ConfigSpace E -> ℝ) : List ℝ :=
  (realValueSet f).sort (· ≤ ·)


noncomputable def realLayers (f : ConfigSpace E -> ℝ) : List (ℝ × ℝ) :=
  layersFrom 0 (realLevels f)


noncomputable def realLayerSet (f : ConfigSpace E -> ℝ) : Finset (ℝ × ℝ) :=
  (realLayers f).toFinset


def realUpperLevel (f : ConfigSpace E -> ℝ) (a : ℝ) : Set (ConfigSpace E) :=
  {omega | a ≤ f omega}

end StatMech.FrontierA
