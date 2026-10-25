/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring


namespace Kaplansky

/-- Projection operator from the projectivity splitting, restricted to an index set `J`. -/
noncomputable def kapProj {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (s : M →ₗ[R] (M →₀ R)) (J : Set M) : M →ₗ[R] M :=
  (Finsupp.linearCombination R (J.indicator fun x => x)) ∘ₗ s

end Kaplansky
