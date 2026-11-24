module
public import Mathlib
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
public import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI
open Set in


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-- **Definition 10.1 (Excisive triple).** *The triple `(X, A, U)` is **excisive** when
`closure U ⊆ interior A`, i.e. the closure of `U` lies in the topological interior of `A`.*

This is the hypothesis under which the excision theorem (Theorem 10.2) asserts that the
inclusion `(X ∖ U, A ∖ U) → (X, A)` induces an isomorphism on relative homology. -/
def IsExcisive (X : Type*) [TopologicalSpace X] (A U : Set X) : Prop :=
  closure U ⊆ interior A

