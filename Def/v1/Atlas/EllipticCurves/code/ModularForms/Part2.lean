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
public import Abbrev.v1.Atlas.EllipticCurves.code.ModularForms.Part2

@[expose] public section

open scoped CongruenceSubgroup MatrixGroups ModularForm Topology Manifold


noncomputable section

section CuspForms

/-- A cusp form for `SL(2, ℤ)` is in particular a modular form (vanishing at cusps
implies boundedness at cusps). -/
def CuspFormForSL2Z.toModularFormForSL2Z {k : ℤ} (f : CuspFormForSL2Z k) :
    ModularFormForSL2Z k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f hc

/-- A cusp form for `SL(2, ℤ)` is in particular a weak modular form (drop both the
boundedness and vanishing conditions at cusps). -/
def CuspFormForSL2Z.toWeakModularForm {k : ℤ} (f : CuspFormForSL2Z k) :
    WeakModularForm (Γ(1) : Subgroup SL(2, ℤ)) k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'

end CuspForms

namespace FLT

/-- The Taylor–Wiles theorem: every semistable elliptic curve over `ℚ` is modular. -/

end FLT

namespace MinimalModel

/-- Predicate stating that an integral Weierstrass model `W` is a model for the
rational Weierstrass curve `E`, i.e. there is a `ℚ`-rational change of variables
taking `W` (viewed over `ℚ`) to `E`. -/
def IsModelFor (E : WeierstrassCurve.Affine ℚ) (W : WeierstrassCurve.Affine ℤ) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange ℚ,
    C • (W.map (Int.castRingHom ℚ)) = E

end MinimalModel
end
