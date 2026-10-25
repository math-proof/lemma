/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Theorem.Combinatorics.SimpleGraph.KneserLovasz
/-!
# Kneser–Lovász theorem

For `0 < k` and `2 * k ≤ n`, the Kneser graph on the `k`-subsets of an
`n`-element set has chromatic number `n - 2 * k + 2`.
-/


namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

open Finset

def knNegLabelEmb {n : ℕ} : (Bool × Fin n) ↪ (Bool × Fin n) :=
  ⟨knNegLabel, knNegLabel_inj⟩

def knNegCell {n : ℕ} (x : Finset (Bool × Fin n)) : Finset (Bool × Fin n) :=
  x.map knNegLabelEmb

def knConsistent {n : ℕ} (x : Finset (Bool × Fin n)) : Prop :=
  ∀ l ∈ x, knNegLabel l ∉ x

def knIsChain {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) : Prop :=
  ∀ a ∈ σ, ∀ b ∈ σ, a ⊆ b ∨ b ⊆ a

def knChain {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) : Prop :=
  σ.Nonempty ∧ (∀ x ∈ σ, knConsistent x) ∧ knIsChain σ

def knTop {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) :
    Finset (Bool × Fin n) :=
  σ.sup id

def knImg {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Finset (Bool × Fin n) :=
  σ.image L

def knHappy {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  knChain σ ∧ knTop σ ⊆ knImg σ L

def knTight {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  knHappy σ L ∧ σ.card = (knTop σ).card

def knLoose {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  knHappy σ L ∧ σ.card = (knTop σ).card + 1

def knAntipodal {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  ∀ x, knConsistent x → x.Nonempty → L (knNegCell x) = knNegLabel (L x)

def knNoCompl {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  ∀ x y, knConsistent x → knConsistent y → x ⊆ y → L y ≠ knNegLabel (L x)

open Classical in
noncomputable def knOut {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Finset (Finset (Bool × Fin n)) :=
  Finset.univ.filter (fun v => v ∉ σ ∧ knChain (insert v σ) ∧ knTop (insert v σ) ⊆ knImg σ L)

open Classical in
noncomputable def knIn {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Finset (Finset (Bool × Fin n)) :=
  σ.filter (fun w => knHappy (σ.erase w) L ∧ knTop σ ⊆ knImg (σ.erase w) L)

def knGAdj {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n)
    (σ τ : Finset (Finset (Bool × Fin n))) : Prop :=
  knHappy σ L ∧ knHappy τ L ∧
    ((∃ v, v ∉ σ ∧ τ = insert v σ ∧ knTop τ ⊆ knImg σ L) ∨
     (∃ w, w ∉ τ ∧ σ = insert w τ ∧ knTop σ ⊆ knImg τ L))

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted
