/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/KaprekarStructuralClassification.lean -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push

section
namespace MetaMathlibExt

private def kapFun (B : ℕ) (d : ℕ × ℕ) : ℕ × ℕ :=
  match List.insertionSort (· ≥ ·)
    (if d.2 = 0 then [d.1 - 1, B - 1, B - 1, B - d.1]
      else [d.1, d.2 - 1, B - d.2 - 1, B - d.1]) with
  | [a, b, c, e] => (a - e, b - c)
  | _ => (0, 0)

private def XBset (B : ℕ) : Set (ℕ × ℕ) := {d | 1 ≤ d.1 ∧ d.1 < B ∧ d.2 ≤ d.1}
private def TBset (B : ℕ) : Set (ℕ × ℕ) :=
  {d | d ∈ XBset B ∧ d.2 < d.1 ∧ 0 < d.2 ∧ Odd d.1 ∧ Odd d.2}

private def dblFun (B : ℕ) (S : Finset (Finset (ZMod B))) : Finset (Finset (ZMod B)) :=
  S.image (fun C => C.image (· * 2))

private def ProjSet (B : ℕ) : Set (Finset (Finset (ZMod B))) :=
  {S | S.card = 2 ∧ ∀ C ∈ S, ∃ x : ZMod B, x ≠ 0 ∧ C = {x, -x}}

/-- Phi bundled as a top-level function (defeq to the lets Phi). -/
private def phiFun (B : ℕ) (d : ↥(TBset B)) : Finset (Finset (ZMod B)) :=
  {{(((d.1.1 + d.1.2) / 2 : ℕ) : ZMod B), -(((d.1.1 + d.1.2) / 2 : ℕ) : ZMod B)},
   ({(((d.1.1 - d.1.2) / 2 : ℕ) : ZMod B), -(((d.1.1 - d.1.2) / 2 : ℕ) : ZMod B)} :
    Finset (ZMod B))}
end MetaMathlibExt
end
