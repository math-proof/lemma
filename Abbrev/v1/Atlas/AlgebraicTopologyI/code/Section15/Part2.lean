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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section15
open Topology


namespace SphereInfty

/-- The Hilbert space $\ell^2(\mathbb{N}, \mathbb{R})$ of square-summable
sequences of real numbers. This serves as the ambient space for the model of
$\mathbb{R}^{\infty}$ and $S^{\infty}$ used below. -/
abbrev l2 := ↥(lp (fun _ : ℕ => ℝ) 2)

end SphereInfty
