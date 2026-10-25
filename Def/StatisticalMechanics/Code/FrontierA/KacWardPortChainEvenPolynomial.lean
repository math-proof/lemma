/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


noncomputable def kwDartEdgeBitValue
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) : Sym2 V -> Fin 2 :=
  Sym2.lift <| ⟨fun v w => if h : G.Adj v w then b.1 ⟨(v, w), h⟩ else 0, by
    intro v w
    dsimp only
    by_cases h : G.Adj v w
    · rw [dif_pos h, dif_pos h.symm]
      exact (b.2 ⟨(v, w), h⟩).symm
    · rw [dif_neg h, dif_neg (fun hwv => h hwv.symm)]⟩

end StatMech.FrontierA
