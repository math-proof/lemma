module
public import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
public import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
public import Def.StatisticalMechanics.Code.FK.EdgeSubsetDomainMarkov
open Finset SimpleGraph
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable instance edgeSubsetFrozenExteriorGraphDecidableAdj
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V)) :
    DecidableRel (edgeSubsetFrozenExteriorGraph K H B psi).Adj :=
  Classical.decRel _


end
end StatMech.FK
