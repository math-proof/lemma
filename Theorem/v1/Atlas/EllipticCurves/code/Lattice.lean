/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Def.v1.Atlas.EllipticCurves.code.Lattice
open Complex Module ZSpan Set

public section

noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- A complex number `x` lies in the lattice `L` iff it has an integer expression
`n₁ ω₁ + n₂ ω₂` in terms of the lattice's periods. -/
theorem mem_lattice_iff {x : ℂ} :
    x ∈ L.lattice ↔ ∃ n₁ n₂ : ℤ, (n₁ : ℂ) * L.ω₁ + (n₂ : ℂ) * L.ω₂ = x :=
  PeriodPair.mem_lattice

end ComplexLattice
end
