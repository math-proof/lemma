module
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section14
public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.UnitInterval
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section15.Part3
open Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
