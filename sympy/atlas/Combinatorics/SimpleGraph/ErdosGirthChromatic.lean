/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ErdosGirthChromatic.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset

private noncomputable def ehgWeight {α : Type*} [Fintype α] [DecidableEq α] (p : ℝ) (E : Finset α) :
    ℝ :=
  p ^ E.card * (1 - p) ^ Eᶜ.card

/-- Cycle-edge set of a cyclic tuple. -/
private def ehgCycleEdges {V : Type*} [DecidableEq V] (j : ℕ) (f : Fin (j + 3) → V) : Finset
    (Sym2 V) :=
  Finset.univ.image (fun i => s(f i, f (i + 1)))

/-- Number of short-cycle witnesses in an edge set. -/
private noncomputable def ehgShortCycleCount (n g : ℕ) (E : Finset (Sym2 (Fin n))) : ℕ :=
  ∑ j ∈ Finset.range (g - 3),
    (Finset.univ.filter (fun f : Fin (j + 3) → Fin n =>
      Function.Injective f ∧ ehgCycleEdges j f ⊆ E)).card

/-- Off-diagonal pairs of a vertex set, as a finset of edges. -/
private noncomputable def ehgOffPairs {n : ℕ} (A : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  A.offDiag.image (Function.uncurry Sym2.mk)

/-- Number of t-sets with no edge inside. -/
private noncomputable def ehgIndepCount (n t : ℕ) (E : Finset (Sym2 (Fin n))) : ℕ :=
  ((Finset.powersetCard t Finset.univ).filter (fun A => Disjoint E (ehgOffPairs A))).card

/-- Vertices deleted to kill all short cycles. -/
private noncomputable def ehgDeleted (n g : ℕ) (E : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  Finset.biUnion (Finset.range (g - 3)) (fun j =>
    (Finset.univ.filter (fun f : Fin (j + 3) → Fin n =>
      Function.Injective f ∧ ehgCycleEdges j f ⊆ E)).image (fun f => f 0))
section
namespace MathlibExt.Combinatorics.SimpleGraph.ErdosGirthChromaticWanted
end MathlibExt.Combinatorics.SimpleGraph.ErdosGirthChromaticWanted
end
