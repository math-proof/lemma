/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.EllipticCurves.code.FermatsLastTheorem.Part3
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.FermatsLastTheorem
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Def.v1.Atlas.EllipticCurves.code.ModularForms
open scoped CongruenceSubgroup MatrixGroups ModularForm Topology Manifold


@[expose] public noncomputable section

section CongruenceSubgroups

/-- Modular forms of weight `k` for the congruence subgroup `Γ₀(N) ≤ SL(2, ℤ)`. -/
abbrev ModularFormGamma0 (N : ℕ) (k : ℤ) :=
  ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k

/-- Weak modular forms of weight `k` for `Γ₀(N)` (holomorphic and slash-invariant,
without cuspidal growth condition). -/
abbrev WeakModularFormGamma0 (N : ℕ) (k : ℤ) :=
  WeakModularForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k

end CongruenceSubgroups

section CuspForms

/-- Cusp forms of weight `k` for the full modular group `SL(2, ℤ) = Γ(1)` (modular
forms vanishing at every cusp). -/
abbrev CuspFormForSL2Z (k : ℤ) := CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k

/-- Cusp forms of weight `k` for the congruence subgroup `Γ₀(N) ≤ SL(2, ℤ)`. -/
abbrev CuspFormGamma0 (N : ℕ) (k : ℤ) :=
  CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k

end CuspForms
end
