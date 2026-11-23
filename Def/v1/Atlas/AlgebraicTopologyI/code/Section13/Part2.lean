/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section12
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section12.Part2
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Normed.Module.Convex
public import Inductive.v1.Atlas.AlgebraicTopologyI.code.Section13

@[expose] public section

open Finset BigOperators Set Metric


namespace AlgebraicTopologyI

/-- The `k`-fold composition of a chain-complex endomorphism `f : C ⟶ C`,
i.e. `f^k`. Used to express iterates of the subdivision operator
`$^k : S_*(X) → S_*(X)` from Lemma 13.4. -/
def endoPow {C : ChainComplex AddCommGrpCat ℕ}
    (f : C ⟶ C) : ℕ → (C ⟶ C)
  | 0 => 𝟙 C
  | n + 1 => f ≫ endoPow f n

end AlgebraicTopologyI
