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
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section15.Part2
open Topology


namespace SphereInfty

/-- The subspace $\mathbb{R}^{\infty} \subseteq \ell^2$ consisting of sequences
with finite support, i.e. those that are nonzero in only finitely many
coordinates. This is the increasing union of all $\mathbb{R}^n$. -/
def RInfty : Set l2 :=
  {x : l2 | Set.Finite (Function.support (x : ℕ → ℝ))}

end SphereInfty
