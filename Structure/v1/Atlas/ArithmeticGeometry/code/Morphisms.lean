/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
public import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
public import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
public import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.VarietyAlgebraEquiv
public import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem1324
public import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
public import Theorem.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv.Part2
public import Theorem.v1.Atlas.ArithmeticGeometry.code.Theorem1324
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order
public import Def.v1.Atlas.ArithmeticGeometry.code.Morphisms


public noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- A homogeneous polynomial of some degree $d$ in $n+1$ variables over $\bar k$:
the package of an underlying polynomial together with the degree witness. -/
structure HomogPoly (n : ℕ) where
  poly : MvPolynomial (Fin (n + 1)) (AlgebraicClosure k)
  deg : ℕ
  isHomog : poly.IsHomogeneous deg

end
