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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section15.Part2
open Topology


namespace SphereInfty

/-- The infinite sphere $S^{\infty} = \mathbb{R}^{\infty} \cap S(\ell^2, 1)$:
unit vectors in $\ell^2$ with finite support. Proposition 15.5 asserts this
space is contractible. -/
abbrev Sphere := ↥(RInfty ∩ Metric.sphere (0 : l2) 1)


end SphereInfty
