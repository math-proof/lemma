/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Matchings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.Convex.Birkhoff

open Finset

namespace Matchings

structure BipartiteGraph (n : ℕ) where
  Adj : Fin n → Fin n → Prop
  [decAdj : DecidablePred (fun p : Fin n × Fin n => Adj p.1 p.2)]

attribute [instance] BipartiteGraph.decAdj

namespace BipartiteGraph

variable {n : ℕ} (G : BipartiteGraph n)

instance (u : Fin n) (v : Fin n) : Decidable (G.Adj u v) :=
  G.decAdj (u, v)

def leftNeighbors (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (G.Adj u)

def rightNeighbors (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => G.Adj u v)

def denseLeft : Prop :=
  ∀ u : Fin n, n ≤ 2 * (G.leftNeighbors u).card

def denseRight : Prop :=
  ∀ v : Fin n, n ≤ 2 * (G.rightNeighbors v).card

end BipartiteGraph

structure PartialMatching {n : ℕ} (G : BipartiteGraph n) where
  edges : Finset (Fin n × Fin n)
  edge_adj : ∀ p ∈ edges, G.Adj p.1 p.2
  left_inj : ∀ ⦃p q⦄, p ∈ edges → q ∈ edges → p.1 = q.1 → p = q
  right_inj : ∀ ⦃p q⦄, p ∈ edges → q ∈ edges → p.2 = q.2 → p = q

namespace PartialMatching

variable {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G)

def matchedLeft : Finset (Fin n) := M.edges.image Prod.fst

def matchedRight : Finset (Fin n) := M.edges.image Prod.snd

def unmatchedLeft : Finset (Fin n) := Finset.univ \ M.matchedLeft

def unmatchedRight : Finset (Fin n) := Finset.univ \ M.matchedRight

def HasAugPath1 {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G) : Prop :=
  ∃ u v, u ∈ M.unmatchedLeft ∧ v ∈ M.unmatchedRight ∧ G.Adj u v

def HasAugPath3 {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G) : Prop :=
  ∃ u v u' v',
    u ∈ M.unmatchedLeft ∧ v ∈ M.unmatchedRight ∧
    (u', v') ∈ M.edges ∧ G.Adj u v' ∧ G.Adj u' v

def HasAugPathLE3 {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G) : Prop :=
  HasAugPath1 M ∨ HasAugPath3 M

structure SizedMatching {n : ℕ} (G : BipartiteGraph n) (k : ℕ) where
  edges : Finset (Fin n × Fin n)
  edge_adj : ∀ p ∈ edges, G.Adj p.1 p.2
  left_inj : ∀ ⦃p q⦄, p ∈ edges → q ∈ edges → p.1 = q.1 → p = q
  right_inj : ∀ ⦃p q⦄, p ∈ edges → q ∈ edges → p.2 = q.2 → p = q
  card_eq : edges.card = k

instance sizedMatchingDecEq {n : ℕ} {G : BipartiteGraph n} {k : ℕ} :
    DecidableEq (SizedMatching G k) := by
  intro a b
  have h : a = b ↔ a.edges = b.edges := by
    constructor
    · intro h; subst h; rfl
    · intro h; cases a; cases b; simp only [SizedMatching.mk.injEq] at h ⊢; exact h
  rw [h]; exact inferInstance

noncomputable instance sizedMatchingFintype {n : ℕ} {G : BipartiteGraph n} {k : ℕ} :
    Fintype (SizedMatching G k) :=
  Fintype.ofInjective SizedMatching.edges (by
    intro a b h; cases a; cases b; simp only [SizedMatching.mk.injEq] at h ⊢; exact h)

def ChainVertex {n : ℕ} (G : BipartiteGraph n) : Type :=
  SizedMatching G n ⊕ SizedMatching G (n - 1)

noncomputable instance chainVertexFintype {n : ℕ} {G : BipartiteGraph n} :
    Fintype (ChainVertex G) :=
  inferInstanceAs (Fintype (SizedMatching G n ⊕ SizedMatching G (n - 1)))

instance chainVertexDecEq {n : ℕ} {G : BipartiteGraph n} :
    DecidableEq (ChainVertex G) :=
  inferInstanceAs (DecidableEq (SizedMatching G n ⊕ SizedMatching G (n - 1)))

abbrev PerfMatching {n : ℕ} (G : BipartiteGraph n) : Type := SizedMatching G n

structure Transition {n : ℕ} (G : BipartiteGraph n) where
  source : ChainVertex G
  target : ChainVertex G

def chainIsAdj {n : ℕ} {G : BipartiteGraph n} (v w : ChainVertex G) : Prop :=
  v = w ∨
  (match v, w with
   | Sum.inl M, Sum.inr M' => M'.edges ⊆ M.edges
   | Sum.inr M', Sum.inl M => M'.edges ⊆ M.edges
   | Sum.inr M₁, Sum.inr M₂ =>
       (M₁.edges \ M₂.edges).card = 1 ∧ (M₂.edges \ M₁.edges).card = 1
   | Sum.inl _, Sum.inl _ => False
  )

def matchingSymDiff {n : ℕ} {G : BipartiteGraph n}
    (s t : PerfMatching G) : Finset (Fin n × Fin n) :=
  (s.edges \ t.edges) ∪ (t.edges \ s.edges)

def chainVertexEdges {n : ℕ} {G : BipartiteGraph n} : ChainVertex G → Finset (Fin n × Fin n)
  | Sum.inl m => m.edges
  | Sum.inr m => m.edges

structure TypeBPathData {n : ℕ} {G : BipartiteGraph n} (T : Transition G)
    (s t : PerfMatching G) where
  removed : Finset (Fin n × Fin n)
  added : Finset (Fin n × Fin n)
  removed_sub : removed ⊆ s.edges
  added_disj : Disjoint added s.edges
  removed_sub_symDiff : removed ⊆ s.edges \ t.edges
  added_sub_symDiff : added ⊆ t.edges \ s.edges
  encodingVertex : ChainVertex G
  encoding_edges_eq : chainVertexEdges encodingVertex = (s.edges \ removed) ∪ added
  canonRemoved : Finset (Fin n × Fin n)
  removed_eq_canon : removed = canonRemoved
  canonAdded : Finset (Fin n × Fin n)
  added_eq_canon : added = canonAdded
  canon_removed_spec : canonRemoved = chainVertexEdges T.source \ chainVertexEdges encodingVertex
  canon_added_spec : canonAdded = chainVertexEdges encodingVertex \ chainVertexEdges T.source
  canonSymDiff : Finset (Fin n × Fin n)
  symDiff_eq_canon : matchingSymDiff s t = canonSymDiff
  canon_symDiff_spec : canonSymDiff =
    (s.edges \ chainVertexEdges encodingVertex) ∪ (chainVertexEdges encodingVertex \ s.edges)

def transitionEncoding {n : ℕ} {G : BipartiteGraph n} {T : Transition G}
    {s t : PerfMatching G} (data : TypeBPathData T s t) : ChainVertex G :=
  data.encodingVertex

def typeBUsesTransition {n : ℕ} {G : BipartiteGraph n}
    (T : Transition G) (s t : PerfMatching G) : Prop :=
  Nonempty (TypeBPathData T s t)

open Classical in

noncomputable def partner {n : ℕ} {G : BipartiteGraph n}
    (augment : SizedMatching G (n - 1) → PerfMatching G)
    (v : ChainVertex G) : PerfMatching G :=
  match v with
  | Sum.inl s => s
  | Sum.inr m => augment m

noncomputable def partnerPreimage {n : ℕ} {G : BipartiteGraph n}
    (augment : SizedMatching G (n - 1) → PerfMatching G)
    (s : PerfMatching G) : Finset (ChainVertex G) :=
  Finset.univ.filter (fun v => partner augment v = s)

inductive PartnerWitness (n : ℕ) where
  | self : PartnerWitness n
  | reduced : Fin n → PartnerWitness n
  | reducedRotated : Fin n → Fin n → PartnerWitness n

def partnerWitnessEquiv (n : ℕ) : PartnerWitness n ≃ (Unit ⊕ Fin n ⊕ (Fin n × Fin n)) where
  toFun := fun x => match x with
    | .self => Sum.inl ()
    | .reduced i => Sum.inr (Sum.inl i)
    | .reducedRotated i j => Sum.inr (Sum.inr (i, j))
  invFun := fun x => match x with
    | Sum.inl () => .self
    | Sum.inr (Sum.inl i) => .reduced i
    | Sum.inr (Sum.inr (i, j)) => .reducedRotated i j
  left_inv := fun x => by cases x <;> rfl
  right_inv := fun x => by
    rcases x with ⟨⟩ | (i | ⟨i, j⟩) <;> rfl

instance partnerWitnessFintype {n : ℕ} : Fintype (PartnerWitness n) :=
  Fintype.ofEquiv _ (partnerWitnessEquiv n).symm


def HasConductanceLB {V : Type*} [Fintype V] [DecidableEq V]
    (cutEdges : Finset V → ℝ) (vol : Finset V → ℝ) (c : ℝ) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    cutEdges S / min (vol S) (vol (Finset.univ \ S)) ≥ c

def HasConductanceUB {V : Type*} [Fintype V] [DecidableEq V]
    (cutEdges : Finset V → ℝ) (vol : Finset V → ℝ) (c : ℝ) : Prop :=
  ∃ S : Finset V, S.Nonempty ∧ S ≠ Finset.univ ∧
    cutEdges S / min (vol S) (vol (Finset.univ \ S)) ≤ c


noncomputable def chainDegree {n : ℕ} {G : BipartiteGraph n}
    (neighbors : ChainVertex G → Finset (ChainVertex G))
    (v : ChainVertex G) : ℕ :=
  (neighbors v).card

noncomputable def chainVol {n : ℕ} {G : BipartiteGraph n}
    (neighbors : ChainVertex G → Finset (ChainVertex G))
    (S : Finset (ChainVertex G)) : ℝ :=
  ∑ v ∈ S, (chainDegree neighbors v : ℝ)

noncomputable def chainCutEdges {n : ℕ} {G : BipartiteGraph n}
    (neighbors : ChainVertex G → Finset (ChainVertex G))
    (S : Finset (ChainVertex G)) : ℝ :=
  ∑ v ∈ S, ((neighbors v).filter (fun w => w ∉ S)).card

def permanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i, A i (σ i)

end Matchings
