/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxFlowMenger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Probability.MaxFlowMenger
open Finset


namespace StatMech

namespace Combinatorics

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}


structure MfmLinkage (G : SimpleGraph V) (A B : Finset V) (n : ℕ) where
  
  src : Fin n → V
  
  tgt : Fin n → V
  
  walk : ∀ i, G.Walk (src i) (tgt i)
  src_mem : ∀ i, src i ∈ A
  tgt_mem : ∀ i, tgt i ∈ B
  isPath : ∀ i, (walk i).IsPath
  disjoint : ∀ ⦃i j⦄, i ≠ j → ∀ v, v ∈ (walk i).support → v ∉ (walk j).support


end Combinatorics
end StatMech
