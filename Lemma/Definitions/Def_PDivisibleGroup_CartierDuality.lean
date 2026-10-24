import Mathlib
import Lemma.Definitions.Def_PDivisibleGroup_Points
import Lemma.Definitions.Def_HopfAlgebra_CartierDual
import Lemma.Definitions.Def_HopfAlgebra_CartierDualInstances

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra WithConv

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ}

structure CartierDuality (G G' : PDivisibleGroup R p h) : Type where

  equiv : ∀ v, G'.level v ≃ₐc[R] CartierDual R (G.level v)

  equiv_transition : ∀ (v : ℕ) (x : G'.level (v + 1)) (a : G.level (v + 1)),
    equiv v (G'.transition v x) (G.transition v a) =
      equiv (v + 1) x (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (v + 1)) p a)

def IsCartierDual (G G' : PDivisibleGroup R p h) : Prop := Nonempty (CartierDuality G G')

namespace CartierDuality

variable {G G' : PDivisibleGroup R p h} (D : CartierDuality G G')

def toDualEquiv (v : ℕ) : G'.level v ≃ₗ[R] Module.Dual R (G.level v) :=
  (D.equiv v).toLinearEquiv.trans (CartierDual.toDual R (G.level v))

@[simp] theorem toDualEquiv_apply (v : ℕ) (x : G'.level v) (a : G.level v) :
    D.toDualEquiv v x a = D.equiv v x a := rfl

theorem toDualEquiv_symm_apply (v : ℕ) (φ : Module.Dual R (G.level v)) :
    (D.toDualEquiv v).symm φ = (D.equiv v).symm (CartierDual.ofDual R (G.level v) φ) := rfl

theorem equiv_mul_apply (v : ℕ) (x y : G'.level v) (a : G.level v) :
    D.equiv v (x * y) a =
      TensorProduct.dualDistrib R (G.level v) (G.level v)
        (CartierDual.toDual R _ (D.equiv v x) ⊗ₜ[R] CartierDual.toDual R _ (D.equiv v y)) (comul (R := R) a) := by
  rw [map_mul]
  exact CartierDual.mul_apply _ _ a

theorem equiv_one_apply (v : ℕ) (a : G.level v) : D.equiv v 1 a = counit (R := R) a := by
  rw [map_one]
  rfl

theorem counit_eq_equiv_apply_one (v : ℕ) (x : G'.level v) : counit (R := R) x = D.equiv v x 1 := by
  rw [← CartierDual.counit_apply (D.equiv v x)]
  exact (CoalgHomClass.counit_comp_apply (D.equiv v) x).symm

variable (L : Type) [CommRing L] [Algebra R L]

def pair (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) : L :=
  ∑ i, Point.toAlgHom f (Module.Free.chooseBasis R (G.level v) i) *
    Point.toAlgHom ψ ((D.toDualEquiv v).symm ((Module.Free.chooseBasis R (G.level v)).coord i))

theorem pair_def (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v f ψ = ∑ i, Point.toAlgHom f (Module.Free.chooseBasis R (G.level v) i) *
      Point.toAlgHom ψ ((D.toDualEquiv v).symm ((Module.Free.chooseBasis R (G.level v)).coord i)) := rfl

end CartierDuality

end PDivisibleGroup

end
