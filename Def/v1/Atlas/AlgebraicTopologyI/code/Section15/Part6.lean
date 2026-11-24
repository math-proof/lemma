module
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section14
public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.UnitInterval
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section15.Part4
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

/-- The standard first basis vector $e_1 = (1, 0, 0, \ldots) \in \ell^2$. This
will be the basepoint to which all of $S^{\infty}$ is contracted. -/
def e1 : l2 := lp.single 2 0 (1 : ℝ)

end SphereInfty
