import Mathlib.Analysis.SpecialFunctions.Exp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorem.Analysis.SpecialFunctions.CompleteExponentialAutonomousFunction
open scoped BigOperators


/-!
# Complete exponential autonomous functions

Source: José Luis López, *Exponential Autonomous Functions*:
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Orozco/orozco5.tex>.
-/


namespace MetaMathlibExt

/-- N-th complete exponential autonomous function of order `k` (`k ≥ 1`), with
parameter `a : Complex` and variables `x = (x₁, …, xₖ)`, as specified in source
statement `jis_4e6064ed86b521df4a4febe5` (concept `jis_sem_2f450d618ad4cc4cadb7505f`).

Initial values: `f 0 = x 0` through `f (k - 1) = x (k - 1)`, `f k = a * exp (x 0)`.
Recurrence: for `n > k`, with `m = n - k ≥ 1`,
`f n = a * exp (x 0) * B m (f 1, …, f m)`, where `B` is the complete Bell
polynomial family `completeBellPolynomial` (argument `i : Nat` standing for
`f (i + 1)`). -/
noncomputable def completeExponentialAutonomousFunction (k : Nat) (hk : 0 < k)
    (a : Complex) (x : Fin k → Complex) : Nat → Complex :=
  fun N =>
    Nat.strongRecOn (motive := fun _ => Complex) N (fun n ih =>
      if h : n < k then x ⟨n, h⟩
      else if _h2 : n = k then a * Complex.exp (x ⟨0, hk⟩)
      else
        a * Complex.exp (x ⟨0, hk⟩) *
          completeBellPolynomial (n - k) (fun i =>
            if h3 : i + 1 < n then ih (i + 1) h3 else 0))

end MetaMathlibExt
