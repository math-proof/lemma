/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part8
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


noncomputable def kwOrderedSplitFinsetExternalBits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (Sym2 (KWDartPort G))) : KWDartEdgeBits G :=
  ⟨fun d => if s(kwPortOfDart G d, kwPortOfDart G d.symm) ∈ F then 1 else 0, by
    intro d
    have hedge : s(kwPortOfDart G d.symm,
        kwPortOfDart G d.symm.symm) =
        s(kwPortOfDart G d, kwPortOfDart G d.symm) := by
      rw [d.symm_symm]
      exact Sym2.eq_swap
    change (if s(kwPortOfDart G d.symm,
        kwPortOfDart G d.symm.symm) ∈ F then 1 else 0) =
      if s(kwPortOfDart G d, kwPortOfDart G d.symm) ∈ F then 1 else 0
    rw [hedge]⟩


noncomputable def kwOrderedSplitFinsetChainField
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G))) : KWPortChainField G :=
  fun v k =>
    if hzero : k = 0 then 0
    else if hlast : k = Fin.last
        (Fintype.card (KWOutgoingDart (G := G) v)) then 0
    else if s(kwPortAtOrderedRank order v (k.pred hzero),
        kwPortAtOrderedRank order v (k.castPred hlast)) ∈ F then 1 else 0

end StatMech.FrontierA
