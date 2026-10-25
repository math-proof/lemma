/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ClawFreeIndependencePoly.lean -/

/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue
/-!
Real-rootedness of the independence polynomial of a claw-free graph
(Chudnovsky–Seymour theorem), via half-plane stability of a weighted
independence sum.
-/


namespace MetaMathlibExt

/-- Claw-free graph: no induced `K₁,₃`, i.e. no center `c` with three
pairwise nonadjacent, mutually distinct neighbors. `independencePoly G`
counts independent vertex sets by size; the wanted theorem says its real
image splits, i.e. it has only real zeros.

Source: Moussa Benoumhani, "On the Modes of the Independence Polynomial of
the Centipede," Journal of Integer Sequences 15 (2012), Article 12.5.1,
unnumbered Chudnovsky–Seymour theorem, lines 142–144,
https://cs.uwaterloo.ca/journals/JIS/VOL15/Benoumhani/benoumhani8.tex
quoting M. Chudnovsky and P. Seymour, "The roots of the independence
polynomial of a clawfree graph," J. Combin. Theory Ser. B 97 (2007), 350–357
(biblio lines 499–501). -/
def clawFree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  ¬ ∃ c l₁ l₂ l₃ : V, c ≠ l₁ ∧ c ≠ l₂ ∧ c ≠ l₃ ∧ l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧
    G.Adj c l₁ ∧ G.Adj c l₂ ∧ G.Adj c l₃ ∧ ¬ G.Adj l₁ l₂ ∧ ¬ G.Adj l₁ l₃ ∧ ¬ G.Adj l₂ l₃

open Classical in
noncomputable def independencePoly {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Polynomial ℤ :=
  Finset.sum (Finset.range (Fintype.card V + 1)) (fun k =>
    ((Finset.univ.filter
      (fun s : Finset V => s.card = k ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ G.Adj a b)).card : ℤ) •
      Polynomial.X ^ k)

/-! ## Private helpers: weighted independence sum and claw-free analysis -/

open Classical in
/-- Independence predicate: all distinct members of `J` are non-adjacent. -/
def cfIndep {V : Type*} (G : SimpleGraph V) (J : Finset V) : Prop :=
  ∀ a ∈ J, ∀ b ∈ J, a ≠ b → ¬ G.Adj a b

open Classical in
/-- Weighted independence sum: `∑ J ⊆ S, [indep J] ∏ x ∈ J, w x * z`. -/
noncomputable def cfZ {V : Type*} [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ)
    (S : Finset V) (z : ℂ) : ℂ :=
  ∑ J ∈ S.powerset, (if cfIndep G J then ∏ x ∈ J, ((w x : ℂ) * z) else 0)

open Classical in
/-- `S` minus the closed neighbourhood of `v`. -/
noncomputable def cfDel {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (v : V) : Finset V :=
  S.filter (fun x => x ≠ v ∧ ¬ G.Adj v x)

/-- Claw-freeness relativized to a finset, in positive form. -/
noncomputable def cfClawFreeOn {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ c ∈ S, ∀ a ∈ S, ∀ b ∈ S, ∀ d ∈ S, G.Adj c a → G.Adj c b → G.Adj c d →
    a ≠ b → a ≠ d → b ≠ d → G.Adj a b ∨ G.Adj a d ∨ G.Adj b d

open Classical in
/-- Private neighbours of `u` (w.r.t. `v`): adjacent to `u`, not to `v`. -/
noncomputable def cfPrivA {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (u v : V) : Finset V :=
  S.filter (fun x => G.Adj u x ∧ x ≠ v ∧ ¬ G.Adj v x)

open Classical in
/-- Private neighbours of `v` (w.r.t. `u`). -/
noncomputable def cfPrivB {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (u v : V) : Finset V :=
  S.filter (fun x => G.Adj v x ∧ x ≠ u ∧ ¬ G.Adj u x)

open Classical in
/-- Vertices of `S` outside both closed neighbourhoods. -/
noncomputable def cfR {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (u v : V) : Finset V :=
  S.filter (fun x => (x ≠ u ∧ ¬ G.Adj u x) ∧ (x ≠ v ∧ ¬ G.Adj v x))

/-- Contracted vertex set `R ∪ A ∪ B`. -/
noncomputable def cfS' {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (u v : V) : Finset V :=
  cfR G S u v ∪ cfPrivA G S u v ∪ cfPrivB G S u v

/-- Contracted graph: add all edges between `A` and `B`. -/
noncomputable def cfContract {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) : SimpleGraph V :=
  G ⊔ SimpleGraph.fromRel (fun x y => x ∈ A ∧ y ∈ B)

open Classical in
/-- Rescaled weight for the contraction: `B` scaled by `s/(s+t)`, `A` by `t/(s+t)`. -/
noncomputable def cfW {V : Type*} [DecidableEq V] (w : V → ℝ)
    (A B : Finset V) (s t : ℝ) : V → ℝ :=
  fun x => if x ∈ B then (s / (s + t)) * w x
    else if x ∈ A then (t / (s + t)) * w x else w x

/-- The upper half-plane plus the point `1`. -/
def cfD : Set ℂ := {z : ℂ | 0 < z.im} ∪ {1}

end MetaMathlibExt

namespace SimpleGraph

/-- Claw-free graph: no induced `K₁,₃`, i.e. no center `c` with three
pairwise nonadjacent, mutually distinct neighbors. Unlike `MetaMathlibExt.clawFree`,
this applies to graphs on arbitrary types. -/
def IsClawFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ ∃ c l₁ l₂ l₃ : V, c ≠ l₁ ∧ c ≠ l₂ ∧ c ≠ l₃ ∧ l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧
    G.Adj c l₁ ∧ G.Adj c l₂ ∧ G.Adj c l₃ ∧ ¬ G.Adj l₁ l₂ ∧ ¬ G.Adj l₁ l₃ ∧ ¬ G.Adj l₂ l₃

end SimpleGraph
