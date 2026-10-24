import Mathlib
import Lemma.Definitions.Def_Dieudonne_DatumAndHonda

set_option autoImplicit false

open scoped TensorProduct
open Deformation

universe u v w

section Realization

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
variable (A : Type v) [CommRing A] [HopfAlgebra k A]

noncomputable def primitives : Submodule k A :=
  LinearMap.ker (Coalgebra.comul (R := k) (A := A)
    - (TensorProduct.mk k A A).flip 1 - TensorProduct.mk k A A 1)

abbrev cotangentSpace : Type v :=
  (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent

structure ModpDieudonneRealization
    [Module.Finite k A] [Module.Free k A] [Coalgebra.IsCocomm k A]
    (D : Type w) [AddCommGroup D] [Module k D] [Module.Finite k D] where

  datum : DieudonneDatum ((p : ℕ) : k) D

  order_eq : Module.finrank k A = p ^ Module.finrank k D

  finrank_kerFrob : Module.finrank k (LinearMap.ker datum.F)
    = Module.finrank k (cotangentSpace k A)

  finrank_kerVer : Module.finrank k (LinearMap.ker datum.V)
    = Module.finrank k (primitives k A)

end Realization
