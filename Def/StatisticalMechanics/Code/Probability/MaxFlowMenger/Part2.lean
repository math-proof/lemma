/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxFlowMenger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Structure.StatisticalMechanics.Code.Probability.MaxFlowMenger
open Finset


namespace StatMech

namespace Combinatorics

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}


def mfm_linkage_mono {H : SimpleGraph V} (h : H ≤ G) {A B : Finset V} {n : ℕ}
    (L : MfmLinkage H A B n) : MfmLinkage G A B n where
  src := L.src
  tgt := L.tgt
  walk i := (L.walk i).mapLe h
  src_mem := L.src_mem
  tgt_mem := L.tgt_mem
  isPath i := by
    rw [Walk.isPath_def, Walk.support_mapLe_eq_support]
    exact (L.isPath i).support_nodup
  disjoint i j hij v hv := by
    rw [Walk.support_mapLe_eq_support] at hv ⊢
    exact L.disjoint hij v hv


end Combinatorics
end StatMech
