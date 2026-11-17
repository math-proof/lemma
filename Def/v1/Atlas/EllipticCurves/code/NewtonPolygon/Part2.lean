/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/NewtonPolygon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Set.Card
public import Class.v1.Atlas.EllipticCurves.code.NewtonPolygon

@[expose] public section

noncomputable section

open scoped Classical

/-- Existence of a `GenusData` instance on every field; the construction is deferred. -/
def FunctionField.genus (k : Type*) [Field k]
    (f : MvPolynomial (Fin 2) k) : ℕ :=
  FunctionField.GenusData.genusVal f

end
