/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.PlusEvenMixing.Part2
open MeasureTheory Set
open scoped BigOperators


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.ConfigSpace StatMech.FK

def currentEvenConfig {E : Type*} (m : InfiniteCurrentConfig E) :
    ConfigSpace E := fun e => decide (Even (m e))

def currentParityTraceTarget {E : Type*} [DecidableEq E]
    (S : Finset E) (odd : ↑S -> Bool) : ConfigSpace E :=
  fun e => if h : e ∈ S then !(odd ⟨e, h⟩) else false

noncomputable def currentParityTraceCoeff {E : Type*} [DecidableEq E]
    (S : Finset E) (odd : ↑S -> Bool) (T : Finset E) : Real :=
  fmu_traceCoef S (currentParityTraceTarget S odd) T

end StatMech.FrontierB
