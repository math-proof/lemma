/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec22GenericSmoothness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec22GenericSmoothness


public noncomputable section

namespace Lec22

open MvPolynomial

/-- Combinatorial proxy for a smooth projective subvariety of `ℙⁿ`: a set of defining
polynomials, the nonzero points on the variety, and the smoothness/dimension data. -/
structure SmoothProjVariety (k : Type*) [CommRing k] (n : ℕ) where
  definingPolys : Set (MvPolynomial (Fin (n + 1)) k)
  points : Set (Fin (n + 1) → k)
  points_nonzero : ∀ x ∈ points, ∃ i : Fin (n + 1), x i ≠ 0
  points_vanish : ∀ x ∈ points, ∀ f ∈ definingPolys, MvPolynomial.eval x f = 0
  dim : ℕ
  smooth : ∀ x ∈ points, ∀ g ∈ definingPolys,
    ∃ i : Fin (n + 1), MvPolynomial.eval x (MvPolynomial.pderiv i g) ≠ 0

end Lec22
end
