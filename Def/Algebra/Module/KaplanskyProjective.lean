/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Kaplansky

/-- Projection operator from the projectivity splitting, restricted to an index set `J`. -/
noncomputable def kapProj {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (s : M →ₗ[R] (M →₀ R)) (J : Set M) : M →ₗ[R] M :=
  (Finsupp.linearCombination R (J.indicator fun x => x)) ∘ₗ s

end Kaplansky
