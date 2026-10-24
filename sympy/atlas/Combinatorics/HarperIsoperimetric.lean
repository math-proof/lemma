/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/HarperIsoperimetric.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import sympy.atlas.InformationTheory.HammingExpansion
import Lemma.Real.HammingExpansion
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Find
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.LinearCombination

section
namespace MathlibExt.Combinatorics.HarperIsoperimetricWanted

/-- Ball volume: partial binomial sum `∑_{i ≤ k} C(n,i)`. -/
private def ballVol (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), n.choose i

/-- Chord index: largest `j ≤ n` with `ballVol n j ≤ m`. -/
private def chordIdx (n m : ℕ) : ℕ :=
  Nat.findGreatest (fun j => ballVol n j ≤ m) n

/-- Chord slope on interval `j`: `C(n,j+2)/C(n,j+1)`. -/
private def chordSlope (n j : ℕ) : ℚ :=
  (n.choose (j + 2) : ℚ) / (n.choose (j + 1) : ℚ)

/-- Chord lower bound on `t = 1` expansion size, as a rational. -/
private def chord (n m : ℕ) : ℚ :=
  if m = 0 then 0
  else (ballVol n (chordIdx n m + 1) : ℚ)
    + chordSlope n (chordIdx n m) * ((m : ℚ) - (ballVol n (chordIdx n m) : ℚ))

private def harperConsEmb (n : ℕ) (b : Bool) :
    (Fin n → Bool) ↪ (Fin (n + 1) → Bool) :=
  ⟨Fin.cons (α := fun _ => Bool) b,
    Fin.cons_right_injective (α := fun _ => Bool) b⟩

private def harperCubeSlice (n : ℕ) (A : Finset (Fin (n + 1) → Bool)) (b : Bool) :
    Finset (Fin n → Bool) :=
  Finset.univ.filter fun y => Fin.cons (α := fun _ => Bool) b y ∈ A
end MathlibExt.Combinatorics.HarperIsoperimetricWanted
end
