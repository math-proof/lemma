import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Exact
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open Finset

section CharacterLattice
variable {ι : Type*} [Fintype ι]


end CharacterLattice

section Pairing
variable {ι : Type*} [Fintype ι]


abbrev componentGroup (e : ι → ℕ) :=
  Module.Dual ℤ (characterLattice ι) ⧸ LinearMap.range (gramMap e)

abbrev componentGroupProj (e : ι → ℕ) :
    Module.Dual ℤ (characterLattice ι) →ₗ[ℤ] componentGroup e :=
  (LinearMap.range (gramMap e)).mkQ

end Pairing

end ModularCurve

end
