/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
public import Mathlib.Data.Fintype.BigOperators
public import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone

@[expose] public section

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- A symmetric matrix $f$ is **indecomposable** iff no proper subset $\emptyset \ne I \subsetneq B$
is "block-diagonal": every such $I$ has a nonzero off-block entry $f_{ij} \ne 0$ with $i \in I$, $j \notin I$. -/
def FormIndecomposable (f : B → B → ℝ) : Prop :=
  ∀ (I : Finset B), I.Nonempty → I ≠ Finset.univ →
    ∃ i ∈ I, ∃ j, j ∉ I ∧ f i j ≠ 0


end CoxeterGroup
