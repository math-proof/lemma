/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearDeletion.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def kwGraphFormalBucketTerm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (r : ℕ) (m : Sym2 V →₀ ℕ) : ℂ :=
  ((∑ loop : Fin (r + 1) → G.Dart,
      if kwGraphLoopExponent G loop = m then
        kwGraphLoopScalar G phase loop
      else 0) / ((r : ℂ) + 1)) * ons_mvMonomialValue weight m

end StatMech.FrontierA
