module

public import Structure.GaloisRep_Residual
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.FieldTheory.Finiteness

set_option autoImplicit false

@[expose] public noncomputable section

open scoped TensorProduct
open Polynomial


namespace ResidualGaloisRep

variable {k : Type} [Field k]

abbrev baseChange (k' : Type) [Field k'] [Algebra k k'] (ρ : ResidualGaloisRep k) :
    ResidualGaloisRep k' :=
  { V := k' ⊗[k] ρ.V
    finrank_eq := by rw [Module.finrank_baseChange, ρ.finrank_eq]
    ρ := { toFun := fun σ => (ρ.ρ σ).baseChange k'
           map_one' := by rw [map_one, LinearMap.baseChange_one]
           map_mul' := fun σ τ => by rw [map_mul, LinearMap.baseChange_mul] }
    factorsThroughFiniteLevel := by
      obtain ⟨L, hL, h1⟩ := ρ.factorsThroughFiniteLevel
      exact ⟨L, hL, fun σ hσ => by
        rw [MonoidHom.coe_mk, OneHom.coe_mk, h1 σ hσ, LinearMap.baseChange_one]⟩ }

end ResidualGaloisRep

end
