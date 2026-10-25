/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.BasedRings
import Abbrev.v1.Atlas.TensorCategories.code.BasedRings
import Mathlib.LinearAlgebra.Dimension.Finrank
import Structure.v1.Atlas.TensorCategories.code.MultifusionSemisimple
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

open Finset Complex


namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (M : MultifusionRingDef ι)

noncomputable section

namespace MfGrRingOfC

variable {M : MultifusionRingDef ι}

/-- Zero element of `MfGrRingOfC M`: the constant-zero coordinate function. -/
instance instZero : Zero (MfGrRingOfC M) := ⟨⟨fun _ => 0⟩⟩

/-- Unit element of `MfGrRingOfC M`: the indicator function of the unit subset `I₀`. -/
instance instOne : One (MfGrRingOfC M) := ⟨⟨fun k => if k ∈ M.I₀ then 1 else 0⟩⟩

/-- Coordinate-wise addition on `MfGrRingOfC M`. -/
instance instAdd : Add (MfGrRingOfC M) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩

/-- Coordinate-wise negation on `MfGrRingOfC M`. -/
instance instNeg : Neg (MfGrRingOfC M) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩

/-- Coordinate-wise subtraction on `MfGrRingOfC M`. -/
instance instSub : Sub (MfGrRingOfC M) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩

/-- Multiplication on `MfGrRingOfC M` given by the structure constants via `mfGrMulC`. -/
instance instMul : Mul (MfGrRingOfC M) := ⟨fun a b => ⟨M.mfGrMulC a.coeff b.coeff⟩⟩

/-- Coordinate-wise `ℕ`-scalar multiplication on `MfGrRingOfC M`. -/
instance instSMulNat : SMul ℕ (MfGrRingOfC M) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Coordinate-wise `ℤ`-scalar multiplication on `MfGrRingOfC M`. -/
instance instSMulInt : SMul ℤ (MfGrRingOfC M) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Natural-number cast into `MfGrRingOfC M`: `m` becomes `m` on the unit subset and `0`
elsewhere. -/
instance instNatCast : NatCast (MfGrRingOfC M) :=
  ⟨fun m => ⟨fun k => if k ∈ M.I₀ then (m : ℂ) else 0⟩⟩

/-- Integer cast into `MfGrRingOfC M`: `m` becomes `m` on the unit subset and `0` elsewhere. -/
instance instIntCast : IntCast (MfGrRingOfC M) :=
  ⟨fun m => ⟨fun k => if k ∈ M.I₀ then (m : ℂ) else 0⟩⟩

end MfGrRingOfC
end
end MultifusionRingDef
