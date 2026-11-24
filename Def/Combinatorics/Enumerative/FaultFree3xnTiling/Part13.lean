module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Instance.Combinatorics.Enumerative.FaultFree3xnTiling


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

def ff3TailCount (R : Type) [Semiring R] (n : ℕ) (p : ff3Profile) : R :=
  ∑ q, (ff3Matrix R ^ n) p q * ff3Boundary R q

def ff3TransferCount (R : Type) [Semiring R] (n : ℕ) : R :=
  ∑ p, ff3Boundary R p * ff3TailCount R n p

def ff3Incoming {n : ℕ} (a : Finset (Fin 3)) (p : Fin n → ff3Profile)
    (j : Fin (n + 1)) : Finset (Fin 3) :=
  if h : j.val = 0 then a else ff3ProfileRows (p ⟨j.val - 1, by omega⟩)

def ff3Outgoing {n : ℕ} (p : Fin n → ff3Profile)
    (j : Fin (n + 1)) : Finset (Fin 3) :=
  if h : j.val < n then ff3ProfileRows (p ⟨j.val, h⟩) else ∅

end MetaMathlibExt
