/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/KurosakiPowerFree.lean -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

section
namespace MetaMathlibExt

namespace Kurosaki

private def kurS01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
private def kurS12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

private def kurTau : ℕ → Equiv.Perm (Fin 3)
  | 0 => kurS01
  | 1 => 1
  | _ + 1 + 1 => kurS12

private def kurGam : ℕ → Equiv.Perm (Fin 3)
  | 0 => 1
  | n + 1 => kurS01 * kurGam ((n + 1) / 3) * kurTau ((n + 1) % 3)
termination_by n => n
decreasing_by
  simp_wf
  omega

private def kurSigFn : Fin 3 → Fin 3 := fun a => if a.val = 0 then 1 else if a.val = 1 then 0 else 2
private def kurRhoFn : Fin 3 → Fin 3 := fun a => if a.val = 1 then 2 else if a.val = 2 then 1 else 0

private def kurW : ℕ → List (Fin 3) := fun n => Nat.rec (motive := fun _ => List (Fin 3))
    [(1 : Fin 3)]
  (fun _ ih => (List.map kurSigFn ih ++ ih) ++ List.map kurRhoFn ih) n

/-- step(k) = γ(k)⁻¹·γ(k+1) -/
private def kurStep (k : ℕ) : Equiv.Perm (Fin 3) := (kurGam k)⁻¹ * kurGam (k + 1)

/-- The six possible 3-blocks. -/
private def kurPerms6 : List (List (Fin 3)) :=
  [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

/-- ω, the infinite ternary word: ω(k) = γ(k)(1). -/
private def kurWord (k : ℕ) : Fin 3 := kurGam k 1

/-- ORep(s, m, p): ω agrees with its p-shift on the window starting at s. -/
private def ORep (s m p : ℕ) : Prop :=
  ∀ i : ℕ, i + p < m → kurWord (s + i) = kurWord (s + i + p)

/-- The 3-block of ω at k. -/
private def kurBlock (k : ℕ) : List (Fin 3) :=
  [kurWord (3 * k), kurWord (3 * k + 1), kurWord (3 * k + 2)]

/-- Step bit: true iff the step is ρ. -/
private def kurStepBit (k : ℕ) : Bool := decide (kurStep k = kurS12)

/-- How a step transforms a block. -/
private def kurStepBlock : Bool → List (Fin 3) → List (Fin 3)
  | false, [x, y, z] => [y, x, z]
  | true, [x, y, z] => [x, z, y]
  | _, l => l

/-- Step bits from k to k+K-1. -/
private def kurBits : ℕ → ℕ → List Bool
  | _, 0 => []
  | k, K + 1 => kurStepBit k :: kurBits (k + 1) K

/-- Local model of a 3(K+1)-letter window of ω. -/
private def kurModelWin : List (Fin 3) → List Bool → List (Fin 3)
  | b, [] => b
  | b, t :: ts => b ++ kurModelWin (kurStepBlock t b) ts

/-- Step-pattern validity. -/
private def kurPatternOK (e : ℕ) (ts : List Bool) : Bool :=
  List.all (List.range ts.length) (fun i =>
    if (e + i) % 3 = 0 then ts[i]? == some false
    else if (e + i) % 3 = 1 then ts[i]? == some true else true)

/-- Mark of a position: agreement at +2 (weight 1) and +3 (weight 2). -/
private def kurMark (x : List (Fin 3)) (i : ℕ) : ℕ :=
  (if x[i]? = x[i + 2]? then 1 else 0) + (if x[i]? = x[i + 3]? then 2 else 0)

/-- Phase detection on a 9-letter window. -/
private def kurPhase9 (x : List (Fin 3)) : ℕ :=
  match [1, 2, 3, 4, 5].find? (fun i => kurMark x i != (kurMark x (i - 1) + 1) % 3) with
  | some i => (3 - i % 3) % 3
  | none => 0

/-- N11(a): finite synchronization table. -/
private def kurSyncCheck : Bool :=
  decide (∀ b ∈ kurPerms6, ∀ e ∈ List.range 3, ∀ t0 t1 t2 : Bool,
    kurPatternOK e [t0, t1, t2] = true → ∀ d ∈ List.range 3,
    kurPhase9 (((kurModelWin b [t0, t1, t2]).drop d).take 9) = d)

/-- N12(a): one row of the finite table: some index disagrees. -/
private def kurSmallRow (b : List (Fin 3)) (ts : List Bool) (d p : ℕ) : Bool :=
  List.any (List.range (7 * p / 4 + 1 - p)) (fun i =>
    decide (¬((kurModelWin b ts)[d + i]? = (kurModelWin b ts)[d + i + p]?)))

/-- N12(a): finite table for the seven small periods. -/
private def kurSmallCheck : Bool :=
  List.all kurPerms6 (fun b =>
    List.all (List.range 3) (fun e =>
      List.all [false, true] (fun t0 =>
        List.all [false, true] (fun t1 =>
          List.all [false, true] (fun t2 =>
            List.all [false, true] (fun t3 =>
              List.all [false, true] (fun t4 =>
                List.all [false, true] (fun t5 =>
                  List.all (List.range 3) (fun d =>
                    List.all [1, 2, 4, 5, 7, 8, 10] (fun p =>
                      if kurPatternOK e [t0, t1, t2, t3, t4, t5]
                      then kurSmallRow b [t0, t1, t2, t3, t4, t5] d p
                      else true))))))))))
end Kurosaki
end MetaMathlibExt
end
