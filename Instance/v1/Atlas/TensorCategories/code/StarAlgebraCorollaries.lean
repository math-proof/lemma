/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Structure.v1.Atlas.TensorCategories.code.StarAlgebraCorollaries
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex

/-- Corollary 1.43.3: a nonzero idempotent in a finite-dimensional `*`-algebra with trace has
positive real trace. -/


namespace StarAlgWithTrace

variable (B : StarAlgWithTrace)

end StarAlgWithTrace

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

noncomputable section

namespace GrRingOfC

variable {R : FusionRing ι}

/-- The zero element of `GrRingOfC R` has all coefficients equal to zero. -/
instance instZero : Zero (GrRingOfC R) := ⟨⟨fun _ => 0⟩⟩

/-- The unit element of `GrRingOfC R` is the indicator function of the multiplicative unit. -/
instance instOne : One (GrRingOfC R) := ⟨⟨fun k => if k = R.unit then 1 else 0⟩⟩

/-- Pointwise addition on `GrRingOfC R`. -/
instance instAdd : Add (GrRingOfC R) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩

/-- Pointwise negation on `GrRingOfC R`. -/
instance instNeg : Neg (GrRingOfC R) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩

/-- Pointwise subtraction on `GrRingOfC R`. -/
instance instSub : Sub (GrRingOfC R) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩

/-- Multiplication on `GrRingOfC R` given by the structure constants `R.N`. -/
instance instMul : Mul (GrRingOfC R) := ⟨fun a b => ⟨R.grMulC a.coeff b.coeff⟩⟩

/-- Pointwise natural-number scalar multiplication on `GrRingOfC R`. -/
instance instSMulNat : SMul ℕ (GrRingOfC R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Pointwise integer scalar multiplication on `GrRingOfC R`. -/
instance instSMulInt : SMul ℤ (GrRingOfC R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- The natural-number cast in `GrRingOfC R` lives entirely at the unit index. -/
instance instNatCast : NatCast (GrRingOfC R) :=
  ⟨fun m => ⟨fun k => if k = R.unit then (m : ℂ) else 0⟩⟩

/-- The integer cast in `GrRingOfC R` lives entirely at the unit index. -/
instance instIntCast : IntCast (GrRingOfC R) :=
  ⟨fun m => ⟨fun k => if k = R.unit then (m : ℂ) else 0⟩⟩

end GrRingOfC
end
end FusionRing
