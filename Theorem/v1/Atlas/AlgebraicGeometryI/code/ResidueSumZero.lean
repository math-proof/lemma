/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSum
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.ResidueSum
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Kaehler.Basic
public import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSumZero

public section

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial Finset BigOperators HahnSeries Classical
  IsDedekindDomain

universe u

variable {k : Type u} [Field k]

namespace ResidueSumZero

/-- Additivity of the residue. -/
lemma laurentResidue_add (f g : LaurentSeries k) :
    laurentResidue (f + g) = laurentResidue f + laurentResidue g := by
  simp [laurentResidue, HahnSeries.coeff_add]

/-- The residue is `k`-linear in the scalar action. -/
lemma laurentResidue_smul (c : k) (f : LaurentSeries k) :
    laurentResidue (c • f) = c * laurentResidue f := by
  simp [laurentResidue, HahnSeries.coeff_smul, smul_eq_mul]

end ResidueSumZero
end
