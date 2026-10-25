import Mathlib
import Theorem.Analysis.Misc.erdos_707


namespace Mainstep

/-- We will show that the following hypotheses are inconsistent; this is the bulk of the proof of Theorem 8. -/
class Hypotheses where
  p : ℕ
  hp : Nat.Prime p
  N : ℕ
  hN : N = p^2 + p + 1
  B: Finset (ZMod N)
  hdiff: IsPerfectDifferenceSet B
  embed : ({1,2,4,8}: Finset ℕ) → B
  h_embed : ∀ n, (embed n).val = n
  h_inj : Function.Injective embed

end Mainstep
