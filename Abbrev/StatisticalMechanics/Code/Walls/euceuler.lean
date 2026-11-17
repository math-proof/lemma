/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
@[expose] public section

open scoped BigOperators
open Finset


namespace StatMech.Euc

abbrev Cell := ℤ × ℤ

abbrev Vtx := ℤ × ℤ


end StatMech.Euc
