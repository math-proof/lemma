/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Characters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RepresentationTheory.Tannaka
public import Mathlib.GroupTheory.ClassEquation
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.Data.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.ToLin
universe u


@[expose] public noncomputable section

open Classical

namespace CharacterTheory

open Representation

abbrev HomG {k : Type u} [CommRing k] {G : Type u} [Monoid G]
    {V : Type u} [AddCommMonoid V] [Module k V]
    {W : Type u} [AddCommMonoid W] [Module k W]
    (ρ : Representation k G V) (ψ : Representation k G W) :=
  ρ.IntertwiningMap ψ

end CharacterTheory
end
