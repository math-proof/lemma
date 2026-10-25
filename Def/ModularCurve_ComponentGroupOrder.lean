import Def.ModularCurve_ComponentGroup
import Theorems.Thm_ModularCurve_gramMap_injective
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open Finset Module

section GramMatrix
variable {ι : Type*} [Fintype ι] {κ : Type*}

def gramMatrixOf (e : ι → ℕ) (v : κ → characterLattice ι) : Matrix κ κ ℤ :=
  Matrix.of fun i j => gramMap e (v i) (v j)

end GramMatrix

section Engine
variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ] {e : ι → ℕ}

def gramRangeBasisOf (he : ∀ x, 0 < e x) (c : Basis κ ℤ (characterLattice ι)) :
    Basis κ ℤ (LinearMap.range (gramMap e)) :=
  c.map (LinearEquiv.ofInjective (gramMap e) (ModularCurve.gramMap_injective he))

end Engine

end ModularCurve

end
