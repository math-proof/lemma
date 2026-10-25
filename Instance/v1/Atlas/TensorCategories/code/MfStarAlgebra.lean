/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean -/

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
import Structure.v1.Atlas.TensorCategories.code.MfStarAlgebra
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex


namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

noncomputable section

namespace MfGrRingOfC

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {R : MultifusionRingDef ι}

/-- Zero element of the complexified Grothendieck ring. -/
instance instZero : Zero (MfGrRingOfC R) := ⟨⟨fun _ => 0⟩⟩

/-- Multiplicative identity of the complexified Grothendieck ring, given by `R.mfOneC`. -/
instance instOne : One (MfGrRingOfC R) := ⟨⟨R.mfOneC⟩⟩

/-- Componentwise addition on the complexified Grothendieck ring. -/
instance instAdd : Add (MfGrRingOfC R) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩

/-- Componentwise negation on the complexified Grothendieck ring. -/
instance instNeg : Neg (MfGrRingOfC R) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩

/-- Componentwise subtraction on the complexified Grothendieck ring. -/
instance instSub : Sub (MfGrRingOfC R) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩

/-- Multiplication on the complexified Grothendieck ring via the structure constants `N`. -/
noncomputable instance instMul : Mul (MfGrRingOfC R) := ⟨fun a b => ⟨R.mfGrMulC a.coeff b.coeff⟩⟩

/-- Componentwise `ℕ`-scalar action on the complexified Grothendieck ring. -/
noncomputable instance instSMulNat : SMul ℕ (MfGrRingOfC R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Componentwise `ℤ`-scalar action on the complexified Grothendieck ring. -/
noncomputable instance instSMulInt : SMul ℤ (MfGrRingOfC R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Natural-number cast on the complexified Grothendieck ring: `m` is the unit `mfOneC`
scaled by `m` on the unit components. -/
instance instNatCast : NatCast (MfGrRingOfC R) :=
  ⟨fun m => ⟨fun k => if k ∈ R.I₀ then (m : ℂ) else 0⟩⟩

/-- Integer cast on the complexified Grothendieck ring: `m` is the unit scaled by `m`
on the unit components. -/
instance instIntCast : IntCast (MfGrRingOfC R) :=
  ⟨fun m => ⟨fun k => if k ∈ R.I₀ then (m : ℂ) else 0⟩⟩

end MfGrRingOfC
end
end MultifusionRingDef
