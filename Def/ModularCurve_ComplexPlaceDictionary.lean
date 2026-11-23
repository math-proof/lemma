module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Analysis.Meromorphic.Order
public import Theorem.HahnSeries.X0
public import Def.ModularCurve_LaurentCoeff
public import Class.AlgebraicCurve_DivisorClassGroup

@[expose] public section

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace ModularCurve

def realize (N : ℕ) (x : LaurentSeries ℂ) (τ : ℍ) : ℂ := by
  classical
  exact
    if H : ∃ p : (k : ℤ) × (ModularForm (CongruenceSubgroup.Gamma0 N) k ×
          ModularForm (CongruenceSubgroup.Gamma0 N) k),
        (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
    then (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ
    else 0

end ModularCurve

end
