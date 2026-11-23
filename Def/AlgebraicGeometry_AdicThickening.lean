module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Instance.AlgebraicGeometry_AdicThickening
public import Abbrev.AlgebraicGeometry_AdicThickening

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R)

def adicThickening (n : ℕ) : Scheme.{u} := pullback f (adicThickeningBase I n)

def adicThickeningι (n : ℕ) : adicThickening f I n ⟶ X := pullback.fst f (adicThickeningBase I n)

def adicThickeningToBase (n : ℕ) : adicThickening f I n ⟶ Spec (.of (R ⧸ I ^ (n + 1))) :=
  pullback.snd f (adicThickeningBase I n)

def adicThickeningTransition (n : ℕ) : adicThickening f I n ⟶ adicThickening f I (n + 1) :=
  pullback.lift (adicThickeningι f I n)
    (adicThickeningToBase f I n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))))
    (by rw [adicThickeningι_comp, Category.assoc, adicThickeningBase_succ_comp])

end AlgebraicGeometry

end

end
