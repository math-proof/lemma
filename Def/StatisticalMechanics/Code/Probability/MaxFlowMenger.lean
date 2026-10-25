/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxFlowMenger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open Finset


namespace StatMech

namespace Combinatorics

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}


def MfmIsABSeparator (G : SimpleGraph V) (A B S : Finset V) : Prop :=
  ∀ ⦃a b : V⦄, a ∈ A → b ∈ B → ∀ (p : G.Walk a b), ∃ v ∈ p.support, v ∈ S


end Combinatorics
end StatMech
