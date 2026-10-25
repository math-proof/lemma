/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.FreeMultipointEdwardsSokal.Part2
import Mathlib.Algebra.BigOperators.Ring.Nat
import Theorem.StatisticalMechanics.Code.FrontierB.FreeParityErrorReduction.Part2
open Set
open scoped BigOperators


namespace StatMech.FK

open StatMech.ConfigSpace

variable {V : Type*} (G : SimpleGraph V)

def allClustersEvenEvent (A : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  {omega | AllClustersEven G omega A}

def twoOddCrossClustersEvent (A B : Finset V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | TwoOddCrossClusters G omega A B}

end StatMech.FK
