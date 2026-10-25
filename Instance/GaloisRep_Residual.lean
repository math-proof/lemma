-- Carved from Lemma/Definitions/Def_GaloisRep_Residual.lean: instance decls only.
import Instance.EllipticCurve_FrobeniusTrace
import Instance.FLTPrelim_Modularity
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finiteness
import Def.GaloisRep_Residual

set_option autoImplicit false

noncomputable section

open scoped WeierstrassCurve.Affine TensorProduct
open Polynomial


instance ResidualGaloisRep.instModuleFinite {k : Type} [Field k] (ρ : ResidualGaloisRep k) :
    Module.Finite k ρ.V :=
  Module.finite_of_finrank_eq_succ ρ.finrank_eq


end
