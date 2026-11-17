module

public import Abbrev.ModularCurve_ComponentGroup
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

set_option autoImplicit false

@[expose] public noncomputable section

namespace ModularCurve

open Finset

section DivisorAction
variable {ι : Type*} [Fintype ι]

abbrev HeckeRowSums (B : Matrix ι ι ℤ) (n : ℤ) : Prop :=
  ∀ i : ι, ∑ j : ι, B i j = n

abbrev HeckeWeightSymm (e : ι → ℕ) (B : Matrix ι ι ℤ) : Prop :=
  ∀ i j : ι, (e j : ℤ) * B i j = (e i : ℤ) * B j i

abbrev HeckeOffDiagDivides (e : ι → ℕ) (B : Matrix ι ι ℤ) : Prop :=
  ∀ i j : ι, i ≠ j → (e i : ℤ) ∣ B i j

end DivisorAction

section Equivariance
variable {ι : Type*} [Fintype ι]

end Equivariance

end ModularCurve
