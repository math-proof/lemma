module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticContinuation.Part2
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.Affine
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part2
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

def sixVertexBetheRootJacobian (N n : Nat) (c : Real)
    (p : Fin n → Real) :
    (Fin n → Real) →L[Real] (Fin n → Real) :=
  fderiv Real (fun q : Fin n → Real =>
    fun j => sixVertexBetheResidual c N n q j) p


end
end StatMech.FrontierD
