import Instance.EllipticCurve_FrobeniusTrace
import Instance.FLTPrelim_Modularity
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finiteness

set_option autoImplicit false

noncomputable section

open scoped WeierstrassCurve.Affine TensorProduct
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
