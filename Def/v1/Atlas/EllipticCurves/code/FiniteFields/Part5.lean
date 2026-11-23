/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Instance.v1.Atlas.EllipticCurves.code.FiniteFields.Part3

@[expose] public section

section Theorem_3_15

open Polynomial IntermediateField

/-- The map from multiplicative generators of `𝔽_{p^n}` to primitive
polynomials of degree `n`, sending `g` to its minimal polynomial over `𝔽_p`. -/
noncomputable def minpoly_of_generator (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1}) :
    {f : (ZMod p)[X] // f.IsPrimitivePolynomial p ∧ f.natDegree = n} :=
  ⟨minpoly (ZMod p) (g.1 : GaloisField p n),
   generator_minpoly_is_prim p n hn g.1 g.2⟩

end Theorem_3_15
