module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceExpansion.Part4
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

open Polynomial


noncomputable def sixVertexMarkedFugacityPolynomial
    (N M k : Nat) : Real[X] :=
  ∑ n ∈ Finset.range (N + 1),
    Polynomial.monomial n (sixVertexMarkedSectorTraceCoefficient N M n k)

end
end StatMech.FrontierD
