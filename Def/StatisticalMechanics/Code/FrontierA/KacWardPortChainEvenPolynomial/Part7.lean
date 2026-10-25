/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part6
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


noncomputable def kwOrderedSplitEdgeBitValue
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) : Sym2 (KWDartPort G) → Fin 2 :=
  Sym2.lift <| ⟨fun p q =>
    if h : (kwOrderedDartPortSplitGraph G order).Adj p q then
      kwOrderedPortSplitAdjBit G order b y p q else 0, by
    intro p q
    dsimp only
    by_cases h : (kwOrderedDartPortSplitGraph G order).Adj p q
    · rw [dif_pos h, dif_pos h.symm]
      exact kwOrderedPortSplitAdjBit_symm G order b y h
    · rw [dif_neg h, dif_neg (fun hqp => h hqp.symm)]⟩

end StatMech.FrontierA
