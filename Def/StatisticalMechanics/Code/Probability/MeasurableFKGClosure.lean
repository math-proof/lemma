module
public import Theorem.StatisticalMechanics.Code.FK.FreeDLRExtreme
public import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part3
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Separation.Profinite
public import Theorem.StatisticalMechanics.Code.Probability.MeasurableFKGClosure
open Filter MeasureTheory Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

variable {E : Type*} [DecidableEq E] [Countable E]

def finiteUpwardHull (F : Finset E) (A : Set (ConfigSpace E)) :
    Set (ConfigSpace E) :=
  {eta | ∃ omega ∈ A, ∀ e ∈ F, omega e ≤ eta e}

end StatMech
