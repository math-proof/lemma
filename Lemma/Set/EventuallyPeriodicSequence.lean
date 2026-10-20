import Mathlib
import sympy.Basic
import sympy.atlas.Dynamics.EventuallyPeriodicSequence
open MetaMathlibExt


/--
[IsEventuallyPeriodic.of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/EventuallyPeriodicSequence.lean)
-/
@[path]
private lemma IsEventuallyPeriodic_of_witness_eq
  {u : ℕ → α}
  {p n₀ : ℕ}
-- given
  (hp : 0 < p)
  (h : ∀ n : ℕ, n₀ ≤ n → u (n + p) = u n) :
-- imply
  IsEventuallyPeriodic u := by
-- proof
  apply MetaMathlibExt.IsEventuallyPeriodic.of_witness hp h

/--
[IsEventuallyPeriodic.witness_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/EventuallyPeriodicSequence.lean)
-/
@[path]
private lemma IsEventuallyPeriodic_witness_spec_eq
  {u : ℕ → α}
-- given
  (h : IsEventuallyPeriodic u) :
-- imply
  ∃ p n₀ : ℕ, 0 < p ∧ ∀ n : ℕ, n₀ ≤ n → u (n + p) = u n := by
-- proof
  apply MetaMathlibExt.IsEventuallyPeriodic.witness_spec h

/--
[IsEventuallyPeriodic.of_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/EventuallyPeriodicSequence.lean)
-/
@[path]
private lemma IsEventuallyPeriodic_of_periodic_eq
  {u : ℕ → α}
  {p : ℕ}
-- given
  (hp : 0 < p)
  (h : ∀ n : ℕ, u (n + p) = u n) :
-- imply
  IsEventuallyPeriodic u := by
-- proof
  apply MetaMathlibExt.IsEventuallyPeriodic.of_periodic hp h

/--
[IsEventuallyPeriodic.of_finite_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/EventuallyPeriodicSequence.lean)
-/
@[path]
private lemma IsEventuallyPeriodic_of_finite_orbit_eq
  [Finite S]
  {F : S → S}
  {r : ℕ → S}
-- given
  (h : ∀ n, r (n + 1) = F (r n)) :
-- imply
  IsEventuallyPeriodic r := by
-- proof
  apply MetaMathlibExt.IsEventuallyPeriodic.of_finite_orbit F r h


-- created on 2026-10-20
