import Mathlib.Analysis.SpecialFunctions.Exp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
open scoped BigOperators


/-!
# Complete exponential autonomous functions

Source: José Luis López, *Exponential Autonomous Functions*:
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Orozco/orozco5.tex>.
-/


namespace MetaMathlibExt

/-- Complete Bell polynomial family `B n`, as used in source statement
`jis_4e6064ed86b521df4a4febe5` (concept `jis_sem_2f450d618ad4cc4cadb7505f`).

`B 0` is `1`, and `B (m + 1)` applied to `x : Nat → Complex` (with `x i`
standing for `y_{i+1}`) is
`∑ i ∈ Finset.range (m + 1), C(m, i) * B (m - i) x * x i`. -/
noncomputable def completeBellPolynomial (n : Nat) (x : Nat → Complex) : Complex :=
  Nat.strongRecOn (motive := fun _ => (Nat → Complex) → Complex) n
    (fun m ih x =>
      match m with
      | 0 => 1
      | m + 1 =>
        ∑ i ∈ Finset.range (m + 1),
          (m.choose i : Complex) * ih (m - i) (by omega) x * x i) x

end MetaMathlibExt
