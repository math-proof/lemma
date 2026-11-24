module
public import Theorem.StatisticalMechanics.Code.FrontierA.ConformalSpinFactor
public import Theorem.StatisticalMechanics.Code.Ising.MagNonneg.Part2
public import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
open BoundedContinuousFunction Filter MeasureTheory Topology
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinConformalReduction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice


noncomputable def spinProdBCF {d : Nat} (A : Finset (Site d)) :
    ConfigSpace (Site d) →ᵇ Real :=
  ∏ x ∈ A, spinBCF x

end StatMech.FrontierA
