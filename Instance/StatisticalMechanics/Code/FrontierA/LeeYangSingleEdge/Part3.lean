/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangDisjointUnion
import Def.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part4
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


instance finiteMatchingDecidableAdj : (n : ℕ) →
    DecidableRel (finiteMatching n).Adj
  | 0 => by
      simp only [finiteMatching]
      infer_instance
  | n + 1 => by
      simp only [finiteMatching]
      letI : DecidableRel (finiteMatching n).Adj := finiteMatchingDecidableAdj n
      infer_instance


end StatMech.FrontierA
