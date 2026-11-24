module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinConformalReduction
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinConformalScaling
open Filter Topology
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinConformalScaling.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable def spinRenormalizedCorrelation
    (iota : Type*) [Fintype iota]
    (delta correlation : Nat → Real) (n : Nat) : Real :=
  spinMeshRenormalization iota (delta n) * correlation n

end StatMech.FrontierA
