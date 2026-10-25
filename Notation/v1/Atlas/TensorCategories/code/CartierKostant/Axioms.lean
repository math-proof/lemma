/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.CoradicalFiltration
import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part8
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.Smooth.Basic
import Def.v1.Atlas.TensorCategories.code.CartierKostant.Axioms.Part2
set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


section UEARange

variable {R : Type u} {H : Type v}

variable [CommRing R] [Ring H] [HopfAlgebra R H]

local notation "SV" => SymmetricAlgebra k V

end UEARange
