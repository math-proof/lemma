/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.GroupTheory.Exponent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.Real.Pi.Bounds
public import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.Isogenies
public import Structure.v1.Atlas.EllipticCurves.code.PointCounting

@[expose] public section

section Lemma71

variable {R : Type*} [Ring R] (IsInsep : R → Prop)

variable {IsInsep}

/-- An equivalence between the points of a Weierstrass curve and `Option`-of-nonsingular
affine pairs: the point at infinity corresponds to `none` and each affine point $(x, y)$
to `some ⟨(x, y), h⟩`. -/
noncomputable def pointEquiv :
    W.Point ≃ Option { p : F × F // W.Nonsingular p.1 p.2 } where
  toFun P := P.rec Option.none (fun x y h => Option.some ⟨⟨x, y⟩, h⟩)
  invFun o := o.rec .zero (fun ⟨⟨x, y⟩, h⟩ => .some x y h)
  left_inv P := by cases P <;> rfl
  right_inv o := by
    cases o with
    | none => rfl
    | some val =>
      obtain ⟨⟨x, y⟩, h⟩ := val
      rfl

end Lemma71
