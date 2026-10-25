import Mathlib
import Def.TateCurve_QShift
import Theorems.Thm_TateCurve_pointX_inv
import Theorems.Thm_TateCurve_pointX_q_mul
import Theorems.Thm_TateCurve_pointX_zpow_mul
import Def.TateCurve_XMultStructure

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section SymPolynomials

variable (q x₁ x₂ : K)


variable {q x₁ x₂}


end SymPolynomials

section Admissibility

variable {q u v w : K}

abbrev OffLattice (q w : K) : Prop := ∀ n : ℤ, q ^ n * w ≠ 1


structure AddParams (q u v : K) : Prop where
  q_ne_zero : q ≠ 0
  u_ne_zero : u ≠ 0
  v_ne_zero : v ≠ 0
  offLattice_u : OffLattice q u
  offLattice_v : OffLattice q v
  offLattice_mul : OffLattice q (u * v)
  offLattice_div : OffLattice q (u * v⁻¹)

namespace AddParams


end AddParams

end Admissibility

section Defects

variable [CompleteSpace K] {q u v w : K}


variable (q u v)


variable {q u v}


end Defects

section Nodal

variable {u v : K}


end Nodal

section Region

variable [CompleteSpace K] {q u v : K}


end Region

end TateCurve

set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section UnitSpectator

variable {q u v : K}


end UnitSpectator

section BoundedDescent

variable (c : ℕ → ℕ → K)


variable {c} {B : ℝ} {w : K}


end BoundedDescent

end TateCurve
