/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section14
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.UnitInterval
import Def.v1.Atlas.AlgebraicTopologyI.code.Section15.Part3
open Topology


namespace SphereInfty

/-- `shiftRight` preserves finite support; used to show $T$ maps
$\mathbb{R}^{\infty}$ into itself. -/
lemma finite_support_shiftRight {x : ℕ → ℝ} (hx : Set.Finite (Function.support x)) :
    Set.Finite (Function.support (shiftRight x)) := by
  apply Set.Finite.subset (hx.image (· + 1))
  intro n hn
  simp only [Function.mem_support] at hn
  cases n with
  | zero => simp [shiftRight] at hn
  | succ n =>
    simp only [Set.mem_image, Function.mem_support]
    exact ⟨n, by intro h; exact hn (by simp [shiftRight, h]), rfl⟩

end SphereInfty
