module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Instance.AlgebraicGeometry_AdicThickening
public import Abbrev.AlgebraicGeometry_AdicThickening

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R)


public theorem adicThickeningι_comp (n : ℕ) :
    adicThickeningι f I n ≫ f = adicThickeningToBase f I n ≫ adicThickeningBase I n :=
  pullback.condition


public theorem adicThickeningBase_succ_comp (n : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))) ≫
      adicThickeningBase I (n + 1) = adicThickeningBase I n := by
  rw [adicThickeningBase, adicThickeningBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.factor_comp_mk]


@[simp] public theorem adicThickeningTransition_ι (n : ℕ) :
    adicThickeningTransition f I n ≫ adicThickeningι f I (n + 1) = adicThickeningι f I n := by
  rw [adicThickeningTransition]; exact pullback.lift_fst _ _ _


public theorem adicThickeningTransition_toBase (n : ℕ) :
    adicThickeningTransition f I n ≫ adicThickeningToBase f I (n + 1) =
      adicThickeningToBase f I n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))) := by
  rw [adicThickeningTransition]; exact pullback.lift_snd _ _ _


public theorem adicThickening_def (n : ℕ) : adicThickening f I n = pullback f (adicThickeningBase I n) := rfl

public theorem adicThickeningι_def (n : ℕ) : adicThickeningι f I n = pullback.fst f (adicThickeningBase I n) := rfl

public theorem adicThickeningToBase_def (n : ℕ) :
    adicThickeningToBase f I n = pullback.snd f (adicThickeningBase I n) := rfl

end AlgebraicGeometry

end
