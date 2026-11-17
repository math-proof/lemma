/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic
public import Structure.v1.Atlas.TensorCategories.code.QuantumGroups
@[expose] public section

set_option maxHeartbeats 800000

universe u v


/-- Reference abbreviation for Definition 1.25.1: the quantum group `U_q(sl_2)`. -/
abbrev def_1_25_1 := @UqSl2


