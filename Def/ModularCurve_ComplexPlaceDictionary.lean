import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Meromorphic.Order
import Lemma.ModularCurve.X0
import Def.ModularCurve_LaurentCoeff
import Class.AlgebraicCurve_DivisorClassGroup

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
