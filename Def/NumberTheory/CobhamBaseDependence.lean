/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CobhamBaseDependence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Data.Set.Basic
public import Abbrev.Dynamics.EventuallyPeriodicSequence
public import Theorem.Set.EventuallyPeriodicSequence
public import Theorem.Nat.BaseRecognizable
public import Def.NumberTheory.BaseRecognizable
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.Tactic

@[expose] public section

namespace MetaMathlibExt

/-- Two natural-number bases are multiplicatively independent when no two
positive powers of them coincide. -/
def BasesMultiplicativelyIndependent (k l : ℕ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → k ^ m ≠ l ^ n

/-- A set of natural numbers is ultimately periodic if membership is periodic
above some threshold, with a positive period. -/
def IsUltimatelyPeriodicSet (S : Set ℕ) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → (n ∈ S ↔ n + p ∈ S)

/-- Zero-padded canonical expansion of `z` to exactly `n` digits. -/
def cbdPad {c : ℕ} (n z : ℕ) (hc : 2 ≤ c) : List (Fin c) :=
  List.replicate (n - (baseDigits hc z).length) ⟨0, by omega⟩ ++ baseDigits hc z

/-- A local period `p` on the interval `[lo, hi]`. -/
def cbdLocalPeriod (S : Set ℕ) (p lo hi : ℕ) : Prop :=
  ∀ u : ℕ, lo ≤ u → u + p ≤ hi → (u ∈ S ↔ u + p ∈ S)

end MetaMathlibExt
