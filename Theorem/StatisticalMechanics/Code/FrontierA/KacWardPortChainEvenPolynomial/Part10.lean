/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part11
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


theorem kwOrderedCanonicalPortChainField_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (b : KWDartEdgeBits G) (hb : KWOriginalPortEven G b) :
    KWOrderedGlobalPortChainEven G order b
      (kwOrderedCanonicalPortChainField G order b) := by
  intro v
  exact ⟨kwPortChainState_zero _, kwPortChainState_succ _,
    (kwPortChainState_last_eq_zero_iff _).2 (by
      rw [kwOrderedExternalPortBits_sum_eq G order b v, hb v])⟩

theorem kwOrderedPortChainField_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (b : KWDartEdgeBits G) (y z : KWPortChainField G)
    (hy : KWOrderedGlobalPortChainEven G order b y)
    (hz : KWOrderedGlobalPortChainEven G order b z) : y = z := by
  funext v
  exact (kwPortChainState_unique _ (y v) (hy v).1 (hy v).2.1).trans
    (kwPortChainState_unique _ (z v) (hz v).1 (hz v).2.1).symm


end StatMech.FrontierA
