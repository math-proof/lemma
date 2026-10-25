/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMFieldOfDefinition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.GroupTheory.GroupAction.Defs


noncomputable section

open Matrix.SpecialLinearGroup Matrix CongruenceSubgroup

open scoped MatrixGroups

namespace CMFieldOfDefinition

/-- The open modular curve $Y(\Gamma) = \Gamma \backslash \mathcal{H}$ as the quotient
of the upper half-plane by the action of a subgroup $\Gamma \leq \mathrm{SL}_2(\mathbb{Z})$
via Mobius transformations. This is the noncompactified moduli space of elliptic curves
with $\Gamma$-level structure. -/
def ModularCurveOpen (Γ : Subgroup SL(2, ℤ)) : Type :=
  Quotient (MulAction.orbitRel Γ UpperHalfPlane)

/-- The extended upper half-plane $\mathcal{H}^* = \mathcal{H} \cup \mathbb{P}^1(\mathbb{Q})$,
the upper half-plane together with the cusps. Adjoining the cusps yields the
compactification used to form projective modular curves. -/
opaque ExtendedUpperHalfPlane : Type

/-- Existence of an action of $\mathrm{SL}_2(\mathbb{Z})$ on the extended upper half-plane
$\mathcal{H}^*$ extending the Mobius action on $\mathcal{H}$ to the cusps. -/
def ModularCurve (Γ : Subgroup SL(2, ℤ)) : Type :=
  Quotient (MulAction.orbitRel Γ ExtendedUpperHalfPlane)

end CMFieldOfDefinition
end
