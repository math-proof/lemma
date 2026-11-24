module
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section14
public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.UnitInterval
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section15.Part2
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

/-- The right-shift operator $T : \ell^2 \to \ell^2$, sending $(x_0, x_1, \ldots)$
to $(0, x_0, x_1, \ldots)$. It is a linear isometry of $\ell^2$ which is *not*
surjective; this defect drives the contraction of $S^{\infty}$. -/
def T (x : l2) : l2 := ⟨shiftRight x.1, memℓp_shiftRight x.2⟩

end SphereInfty
