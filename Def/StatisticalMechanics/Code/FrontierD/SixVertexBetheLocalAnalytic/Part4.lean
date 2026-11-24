module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticContinuation.Part2
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.Affine
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part4
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheContinuationSet
    (a b : Real) (N n : Nat) : Set (Real × (Fin n → Real)) :=
  {q | q.1 ∈ Set.Icc a b ∧ SixVertexClosedRootSimplex q.2 ∧
    sixVertexBetheUpdate q.1 N n q.2 = q.2}

end
end StatMech.FrontierD
