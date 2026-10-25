/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRoch
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRoch
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSheavesCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GrothendieckBirkhoff
import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.GrothendieckBirkhoff
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Fin.VecNotation
open BigOperators


namespace GBExistence

/-- Combinatorial model for `h⁰(P¹, O(d)) = max(d + 1, 0)`. -/
def h0_dim (d : ℤ) : ℕ := Int.toNat (d + 1)

/-- Combinatorial model for `h¹(P¹, O(d)) = max(−d − 1, 0)` (Serre duality). -/
def h1_dim (d : ℤ) : ℕ := Int.toNat (-d - 1)

/-- Total `h⁰` of a direct sum `⊕ O(d_i)` indexed by `Fin n`. -/
def h0_total {n : ℕ} (degrees : Fin n → ℤ) : ℕ :=
  ∑ i, h0_dim (degrees i)

/-- Total `h¹` of a direct sum `⊕ O(d_i)` indexed by `Fin n`. -/
def h1_total {n : ℕ} (degrees : Fin n → ℤ) : ℕ :=
  ∑ i, h1_dim (degrees i)

/-- Dimension of `Ext¹(O(a), O(b)) = H¹(O(b − a))` on `P¹`. -/
def ext1_dim (a b : ℤ) : ℕ := h1_dim (b - a)

end GBExistence
