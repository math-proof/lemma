/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/HarperIsoperimetric.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Def.InformationTheory.HammingExpansion
public import Theorem.Real.HammingExpansion
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Find
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Tactic.LinearCombination

@[expose] public section

section

namespace MathlibExt.Combinatorics.HarperIsoperimetricWanted

/-- Ball volume: partial binomial sum `∑_{i ≤ k} C(n,i)`. -/
def ballVol (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), n.choose i

/-- Chord index: largest `j ≤ n` with `ballVol n j ≤ m`. -/
def chordIdx (n m : ℕ) : ℕ :=
  Nat.findGreatest (fun j => ballVol n j ≤ m) n

/-- Chord slope on interval `j`: `C(n,j+2)/C(n,j+1)`. -/
def chordSlope (n j : ℕ) : ℚ :=
  (n.choose (j + 2) : ℚ) / (n.choose (j + 1) : ℚ)

/-- Chord lower bound on `t = 1` expansion size, as a rational. -/
def chord (n m : ℕ) : ℚ :=
  if m = 0 then 0
  else (ballVol n (chordIdx n m + 1) : ℚ)
    + chordSlope n (chordIdx n m) * ((m : ℚ) - (ballVol n (chordIdx n m) : ℚ))

def harperConsEmb (n : ℕ) (b : Bool) :
    (Fin n → Bool) ↪ (Fin (n + 1) → Bool) :=
  ⟨Fin.cons (α := fun _ => Bool) b,
    Fin.cons_right_injective (α := fun _ => Bool) b⟩

def harperCubeSlice (n : ℕ) (A : Finset (Fin (n + 1) → Bool)) (b : Bool) :
    Finset (Fin n → Bool) :=
  Finset.univ.filter fun y => Fin.cons (α := fun _ => Bool) b y ∈ A

end MathlibExt.Combinatorics.HarperIsoperimetricWanted
end
