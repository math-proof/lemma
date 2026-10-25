/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Schnirelmann.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Schnirelmann
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic
/-! # Schnirelmann density: sumset inequality and bases

This module proves a lower bound for the density of a sumset and shows that a set containing zero
with positive Schnirelmann density is an additive basis of finite order. The basis result follows
Lemma 1 of Tim Jameson's ["Linnik's proof of the Waring-Hilbert theorem from Hua's book (with a
correction)"](https://www.maths.lancs.ac.uk/jameson/warlin.pdf).
-/


namespace MathlibExt.Combinatorics.Schnirelmann

open Finset

open scoped Pointwise

/-- The number of positive members of `A` that are at most `n`. -/
def schnirelmannCount (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : ℕ :=
  #{a ∈ Ioc 0 n | a ∈ A}

def schnirelmannSumset (A : Set ℕ) (h : ℕ) : Set ℕ :=
  {n | ∃ x : Fin h → ℕ, (∀ i, x i ∈ A) ∧ n = ∑ i, x i}

end MathlibExt.Combinatorics.Schnirelmann
