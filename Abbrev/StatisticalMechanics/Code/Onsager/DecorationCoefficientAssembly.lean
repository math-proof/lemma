module
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
public import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
public import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientInduction.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationCoefficientAssembly


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCoefficientAssembly.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising


abbrev ons_DecoratedContainingEdge
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :=
  {D : ons_DecoratedEvenSubgraph L //
    s(d, ons_dartRev L d) ∈ D.1}


end StatMech.Onsager
