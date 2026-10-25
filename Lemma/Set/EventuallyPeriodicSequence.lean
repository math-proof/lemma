import Mathlib
import sympy.Basic
import Abbrev.Dynamics.EventuallyPeriodicSequence
open MetaMathlibExt


namespace MetaMathlibExt

/--
[IsEventuallyPeriodic.of_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/EventuallyPeriodicSequence.lean)
-/
@[path]
lemma IsEventuallyPeriodic.of_periodic
  {u : ℕ → α}
  {p : ℕ}
-- given
  (hp : 0 < p)
  (h : ∀ n : ℕ, u (n + p) = u n) :
-- imply
  IsEventuallyPeriodic u :=
-- proof
  ⟨p, 0, hp, fun n _ => h n⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsEventuallyPeriodic.of_finite_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/EventuallyPeriodicSequence.lean)
-/
@[path]
lemma IsEventuallyPeriodic.of_finite_orbit
  [Finite S]
  {F : S → S}
  {r : ℕ → S}
-- given
  (h : ∀ n, r (n + 1) = F (r n)) :
-- imply
  IsEventuallyPeriodic r := by
-- proof
  obtain ⟨x, y, hne, hxy⟩ := Finite.exists_ne_map_eq_of_infinite r
  wlog hlt : x < y generalizing x y
  · exact this y x hne.symm hxy.symm (by omega)
  refine ⟨y - x, x, by omega, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero => simpa [Nat.add_sub_cancel' hlt.le] using hxy.symm
  | succ d ih =>
    rw [show x + (d + 1) + (y - x) = x + d + (y - x) + 1 by omega, ← add_assoc, h, h,
      ih (by omega)]

end MetaMathlibExt

/--
[IsEventuallyPeriodic.of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/EventuallyPeriodicSequence.lean)
-/
@[path]
lemma IsEventuallyPeriodic.of_witness
  {u : ℕ → α}
  {p n₀ : ℕ}
-- given
  (hp : 0 < p)
  (h : ∀ n : ℕ, n₀ ≤ n → u (n + p) = u n) :
-- imply
  IsEventuallyPeriodic u :=
-- proof
  ⟨p, n₀, hp, h⟩


namespace MetaMathlibExt

/--
[IsEventuallyPeriodic.witness_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/EventuallyPeriodicSequence.lean)
-/
@[path]
lemma IsEventuallyPeriodic.witness_spec
  {u : ℕ → α}
-- given
  (h : IsEventuallyPeriodic u) :
-- imply
  ∃ p n₀ : ℕ, 0 < p ∧ ∀ n : ℕ, n₀ ≤ n → u (n + p) = u n :=
-- proof
  h

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
