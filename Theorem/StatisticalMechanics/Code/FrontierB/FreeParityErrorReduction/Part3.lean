/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.FreeMultipointEdwardsSokal.Part2
import Mathlib.Algebra.BigOperators.Ring.Nat
import Def.StatisticalMechanics.Code.FrontierB.FreeParityErrorReduction.Part3
open Set
open scoped BigOperators


namespace StatMech.FK

open StatMech.ConfigSpace

variable {V : Type*} (G : SimpleGraph V)

theorem allClustersEven_factorization_error_subset
    [DecidableEq V] (A B : Finset V) (hdisj : Disjoint A B)
    (hAcard : Even A.card) (hBcard : Even B.card) :
    allClustersEvenEvent G (A ∪ B) \ 
        (allClustersEvenEvent G A ∩ allClustersEvenEvent G B) ⊆
      twoOddCrossClustersEvent G A B := by
  intro omega homega
  exact allClustersEven_union_error_subset_twoOddCrossClusters G omega A B
    hdisj hAcard hBcard homega.1 homega.2

end StatMech.FK
