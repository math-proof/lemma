module
public import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
public import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
public import Def.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness.Part2
open scoped BigOperators
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

instance instDecidablePathContainsWord {E : Type*} [DecidableEq E]
    {m k n : ℕ} (p : Fin (k + 1) → E) (q : Fin (m + (n + k) + 1) → E) :
    Decidable (pathContainsWord p q) := by
  unfold pathContainsWord
  infer_instance

end StatMech.FrontierB
