/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.SAW

@[expose] public section


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


abbrev ZdSite (d : ℕ) : Type := Fin d → ℤ


abbrev ZdStep (d : ℕ) : Type := Fin d × Bool


end StatMech.Universality
