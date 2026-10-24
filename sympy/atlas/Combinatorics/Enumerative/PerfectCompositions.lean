/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PerfectCompositions.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

section

namespace MetaMathlibExt

/-- Expansion of symbolic runs into plain parts. -/
private def expandSym (S : List (ℕ × ℕ)) : List ℕ :=
  S.flatMap fun p => List.replicate p.2 p.1

/-- Canonical realization of a count function: take `c p.1` copies from each run. -/
private def canonSym (S : List (ℕ × ℕ)) (c : ℕ → ℕ) : List ℕ :=
  S.flatMap fun p => List.replicate (c p.1) p.1

/-- Insert a run into a fst-sorted list. -/
private def insByFst (p : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [p]
  | q :: S => if p.1 ≤ q.1 then p :: q :: S else q :: insByFst p S

/-- Insertion sort by first component. -/
private def isortByFst : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | q :: S => insByFst q (isortByFst S)
end MetaMathlibExt
