/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


def kwFinsetDartEdgeBits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (Sym2 V)) : KWDartEdgeBits G :=
  ⟨fun d => if d.edge ∈ F then 1 else 0, by
    intro d
    change (if d.symm.edge ∈ F then 1 else 0) =
      if d.edge ∈ F then 1 else 0
    rw [d.edge_symm]⟩

end StatMech.FrontierA
