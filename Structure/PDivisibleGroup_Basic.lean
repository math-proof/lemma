import Mathlib
import Instance.PDivisibleGroup_Basic

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

universe u v w

namespace PDivisibleGroup.Hopf

section NSMul

variable (R : Type u) [CommSemiring R] (A : Type v) [CommSemiring A] [Bialgebra R A]

noncomputable def nsmulAlgHom (n : ℕ) : A →ₐ[R] A :=
  ((toConv (AlgHom.id R A)) ^ n).ofConv


variable {R A}


end NSMul

section Ideals

variable (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Bialgebra R A]

def augIdeal : Ideal A := RingHom.ker (counitAlgHom R A)


noncomputable def torsionIdeal (n : ℕ) : Ideal A := (augIdeal R A).map (nsmulAlgHom R A n)


end Ideals

end PDivisibleGroup.Hopf

structure PDivisibleGroup (R : Type) [CommRing R] (p h : ℕ) : Type 1 where

  level : ℕ → Type
  [instCommRing : ∀ v, CommRing (level v)]
  [instHopfAlgebra : ∀ v, HopfAlgebra R (level v)]
  [instIsCocomm : ∀ v, Coalgebra.IsCocomm R (level v)]
  [instModuleFinite : ∀ v, Module.Finite R (level v)]
  [instModuleFree : ∀ v, Module.Free R (level v)]

  transition : ∀ v, level (v + 1) →ₐc[R] level v
  transition_surjective : ∀ v, Function.Surjective (transition v)

  finrank_level : ∀ v, Module.finrank R (level v) = p ^ (v * h)

  ker_transition : ∀ v,
    RingHom.ker (transition v) = PDivisibleGroup.Hopf.torsionIdeal R (level (v + 1)) (p ^ v)

attribute [instance] PDivisibleGroup.instCommRing PDivisibleGroup.instHopfAlgebra
  PDivisibleGroup.instIsCocomm PDivisibleGroup.instModuleFinite PDivisibleGroup.instModuleFree

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)


end PDivisibleGroup
