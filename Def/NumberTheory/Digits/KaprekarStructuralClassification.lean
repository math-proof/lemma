/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/KaprekarStructuralClassification.lean -/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.List.Sort
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Push

@[expose] public section

section

namespace MetaMathlibExt

def kapFun (B : ℕ) (d : ℕ × ℕ) : ℕ × ℕ :=
  match List.insertionSort (· ≥ ·)
    (if d.2 = 0 then [d.1 - 1, B - 1, B - 1, B - d.1]
      else [d.1, d.2 - 1, B - d.2 - 1, B - d.1]) with
  | [a, b, c, e] => (a - e, b - c)
  | _ => (0, 0)

def XBset (B : ℕ) : Set (ℕ × ℕ) := {d | 1 ≤ d.1 ∧ d.1 < B ∧ d.2 ≤ d.1}

def TBset (B : ℕ) : Set (ℕ × ℕ) :=
  {d | d ∈ XBset B ∧ d.2 < d.1 ∧ 0 < d.2 ∧ Odd d.1 ∧ Odd d.2}

def dblFun (B : ℕ) (S : Finset (Finset (ZMod B))) : Finset (Finset (ZMod B)) :=
  S.image (fun C => C.image (· * 2))

def ProjSet (B : ℕ) : Set (Finset (Finset (ZMod B))) :=
  {S | S.card = 2 ∧ ∀ C ∈ S, ∃ x : ZMod B, x ≠ 0 ∧ C = {x, -x}}

/-- Phi bundled as a top-level function (defeq to the lets Phi). -/
def phiFun (B : ℕ) (d : ↥(TBset B)) : Finset (Finset (ZMod B)) :=
  {{(((d.1.1 + d.1.2) / 2 : ℕ) : ZMod B), -(((d.1.1 + d.1.2) / 2 : ℕ) : ZMod B)},
   ({(((d.1.1 - d.1.2) / 2 : ℕ) : ZMod B), -(((d.1.1 - d.1.2) / 2 : ℕ) : ZMod B)} :
    Finset (ZMod B))}

end MetaMathlibExt
end
