import Abbrev.ModularCurve_ComponentGroup
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

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
