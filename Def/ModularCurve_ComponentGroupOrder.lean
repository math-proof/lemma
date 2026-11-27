module
public import Def.ModularCurve_ComponentGroup
public import Theorem.Thm_ModularCurve_gramMap_injective
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
set_option autoImplicit false


public section

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
