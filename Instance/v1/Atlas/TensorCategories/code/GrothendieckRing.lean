/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Structure.v1.Atlas.TensorCategories.code.GrothendieckRing
set_option maxHeartbeats 800000

open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

namespace GrRingOf

variable {R : FusionRing ι}

/-- Zero element of `GrRingOf R`. -/
instance : Zero (GrRingOf R) := ⟨⟨fun _ => 0⟩⟩

/-- Multiplicative identity of `GrRingOf R`, given by `R.grOne`. -/
instance : One (GrRingOf R) := ⟨⟨R.grOne⟩⟩

/-- Pointwise addition on `GrRingOf R`. -/
instance : Add (GrRingOf R) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩

/-- Pointwise negation on `GrRingOf R`. -/
instance : Neg (GrRingOf R) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩

/-- Pointwise subtraction on `GrRingOf R`. -/
instance : Sub (GrRingOf R) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩

/-- Fusion multiplication on `GrRingOf R`. -/
instance : Mul (GrRingOf R) := ⟨fun a b => ⟨R.grMul a.coeff b.coeff⟩⟩

/-- Pointwise `ℕ`-scalar multiplication on `GrRingOf R`. -/
instance : SMul ℕ (GrRingOf R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Pointwise `ℤ`-scalar multiplication on `GrRingOf R`. -/
instance : SMul ℤ (GrRingOf R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Embedding of `ℕ` into `GrRingOf R` as multiples of the unit basis element. -/
instance : NatCast (GrRingOf R) := ⟨fun m => ⟨fun k => if k = R.unit then (m : ℤ) else 0⟩⟩

/-- Embedding of `ℤ` into `GrRingOf R` as multiples of the unit basis element. -/
instance : IntCast (GrRingOf R) := ⟨fun m => ⟨fun k => if k = R.unit then (m : ℤ) else 0⟩⟩

end GrRingOf
end FusionRing
