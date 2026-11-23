/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section14
public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.UnitInterval
public import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section15.Part2

@[expose] public section

open Topology


namespace SphereInfty

/-- The subspace $\mathbb{R}^{\infty} \subseteq \ell^2$ consisting of sequences
with finite support, i.e. those that are nonzero in only finitely many
coordinates. This is the increasing union of all $\mathbb{R}^n$. -/
def RInfty : Set l2 :=
  {x : l2 | Set.Finite (Function.support (x : ℕ → ℝ))}

end SphereInfty
