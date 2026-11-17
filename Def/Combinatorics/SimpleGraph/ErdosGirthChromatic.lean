/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ErdosGirthChromatic.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

open Finset


noncomputable def ehgWeight {α : Type*} [Fintype α] [DecidableEq α] (p : ℝ) (E : Finset α) :
    ℝ :=
  p ^ E.card * (1 - p) ^ Eᶜ.card

/-- Cycle-edge set of a cyclic tuple. -/
def ehgCycleEdges {V : Type*} [DecidableEq V] (j : ℕ) (f : Fin (j + 3) → V) : Finset
    (Sym2 V) :=
  Finset.univ.image (fun i => s(f i, f (i + 1)))

/-- Number of short-cycle witnesses in an edge set. -/
noncomputable def ehgShortCycleCount (n g : ℕ) (E : Finset (Sym2 (Fin n))) : ℕ :=
  ∑ j ∈ Finset.range (g - 3),
    (Finset.univ.filter (fun f : Fin (j + 3) → Fin n =>
      Function.Injective f ∧ ehgCycleEdges j f ⊆ E)).card

/-- Off-diagonal pairs of a vertex set, as a finset of edges. -/
noncomputable def ehgOffPairs {n : ℕ} (A : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  A.offDiag.image (Function.uncurry Sym2.mk)

/-- Number of t-sets with no edge inside. -/
noncomputable def ehgIndepCount (n t : ℕ) (E : Finset (Sym2 (Fin n))) : ℕ :=
  ((Finset.powersetCard t Finset.univ).filter (fun A => Disjoint E (ehgOffPairs A))).card

/-- Vertices deleted to kill all short cycles. -/
noncomputable def ehgDeleted (n g : ℕ) (E : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  Finset.biUnion (Finset.range (g - 3)) (fun j =>
    (Finset.univ.filter (fun f : Fin (j + 3) → Fin n =>
      Function.Injective f ∧ ehgCycleEdges j f ⊆ E)).image (fun f => f 0))

