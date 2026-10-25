/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Characters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Tannaka
import Mathlib.GroupTheory.ClassEquation
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Data.Matrix.Action
import Mathlib.LinearAlgebra.Matrix.ToLin
universe u


noncomputable section

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
