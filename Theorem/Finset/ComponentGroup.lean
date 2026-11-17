module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Algebra.Exact
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Def.ModularCurve_ComponentGroup
public import Abbrev.ModularCurve_ComponentGroup

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open Finset

section CharacterLattice
variable {ι : Type*} [Fintype ι]


@[simp] public theorem degreeOn_apply (D : ι → ℤ) : degreeOn ι D = ∑ x : ι, D x := by
  simp [degreeOn]


public theorem mem_characterLattice {D : ι → ℤ} :
    D ∈ characterLattice ι ↔ ∑ x : ι, D x = 0 := by
  simp [characterLattice, LinearMap.mem_ker]

end CharacterLattice

section Pairing
variable {ι : Type*} [Fintype ι]


@[simp] public theorem widthPairing_apply (e : ι → ℕ) (D D' : ι → ℤ) :
    widthPairing e D D' = ∑ x : ι, (e x : ℤ) * (D x * D' x) :=
  rfl

public theorem widthPairing_comm (e : ι → ℕ) (D D' : ι → ℤ) :
    widthPairing e D D' = widthPairing e D' D := by
  simp only [widthPairing_apply]
  exact Finset.sum_congr rfl fun x _ => by ring


@[simp] public theorem gramMap_apply (e : ι → ℕ) (D D' : characterLattice ι) :
    gramMap e D D' = ∑ x : ι, (e x : ℤ) * (D.1 x * D'.1 x) :=
  rfl

end Pairing

end ModularCurve

end
