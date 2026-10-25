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
import Structure.v1.Atlas.AlgebraicGeometryI.code.GBSplittingExistence
open BigOperators


namespace GBExistence

/-- `h⁰(⊕ O(d_i + t))` for a splitting type `s` twisted by `t`. -/
def SplittingType.h0_twisted {n : ℕ} (s : SplittingType n) (t : ℤ) : ℕ :=
  ∑ i, h0_dim (s.degrees i + t)

/-- `h¹(⊕ O(d_i + t))` for a splitting type `s` twisted by `t`. -/
def SplittingType.h1_twisted {n : ℕ} (s : SplittingType n) (t : ℤ) : ℕ :=
  ∑ i, h1_dim (s.degrees i + t)

/-- The maximum degree `d_1` in a non-empty splitting type. -/
def SplittingType.maxDegree {n : ℕ} (s : SplittingType (n + 1)) : ℤ :=
  s.degrees ⟨0, Nat.zero_lt_succ n⟩

/-- The splitting type obtained by removing the first (maximal) summand. -/
def SplittingType.tail {n : ℕ} (s : SplittingType (n + 1)) : SplittingType n where
  degrees := fun i => s.degrees (Fin.succ i)
  sorted := fun i j hij =>
    s.sorted (Fin.succ i) (Fin.succ j) (Fin.succ_le_succ_iff.mpr hij)

end GBExistence
