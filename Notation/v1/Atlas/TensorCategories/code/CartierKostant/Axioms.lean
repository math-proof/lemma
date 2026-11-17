/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
public import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part8
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.Smooth.Basic
public import Def.v1.Atlas.TensorCategories.code.CartierKostant.Axioms.Part2

public section

set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


section UEARange

variable {R : Type u} {H : Type v}

variable [CommRing R] [Ring H] [HopfAlgebra R H]

local notation "SV" => SymmetricAlgebra k V

end UEARange
