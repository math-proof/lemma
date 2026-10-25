/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UniqueGames.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Field
import Def.v1.Atlas.BooleanFunctions.code.PCP.Part5
import Theorem.v1.Atlas.BooleanFunctions.code.MISBound
import Structure.v1.Atlas.BooleanFunctions.code.UniqueGames.Part4


namespace UniqueGames

variable {X : Type*} [DecidableEq X] [Fintype X] {k : ℕ}

def numCutEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : MaxCutInstance V) (f : V → Bool) : ℕ :=
  (G.edges.filter (fun e => f e.1 ≠ f e.2)).card

noncomputable def cutFraction {V : Type*} [Fintype V] [DecidableEq V]
    (G : MaxCutInstance V) (f : V → Bool) : ℝ :=
  (numCutEdges G f : ℝ) / (G.edges.card : ℝ)

noncomputable def value {V : Type*} [Fintype V] [DecidableEq V]
    (G : MaxCutInstance V) : ℝ :=
  iSup (fun f : V → Bool => cutFraction G f)

noncomputable def goemansWilliamsonConstant : ℝ :=
  ⨅ θ ∈ Set.Ioo (0 : ℝ) Real.pi, (2 / Real.pi) * θ / (1 - Real.cos θ)

def IsPolyTimeMaxCutInstanceReduction {numVerts : ℕ → ℕ}
    (_ : ∀ (m : ℕ), PCP.BinaryString m → MaxCutInstance (Fin (numVerts m))) : Prop :=
  ∃ (steps : ℕ → ℕ), PCP.IsPolynomial steps ∧ ∀ (m : ℕ), numVerts m ≤ steps m

def IsNPHardGapMaxCut (c s : ℝ) : Prop :=
  ∀ (L : PCP.Language), PCP.InNP L →
    ∃ (numVerts : ℕ → ℕ) (reduce : ∀ (m : ℕ), PCP.BinaryString m → MaxCutInstance (Fin (numVerts m))),
      PCP.IsPolynomial numVerts ∧
      IsPolyTimeMaxCutInstanceReduction reduce ∧
      (∀ (m : ℕ) (x : PCP.BinaryString m), x ∈ L m → value (reduce m x) ≥ c) ∧
      (∀ (m : ℕ) (x : PCP.BinaryString m), x ∉ L m → value (reduce m x) ≤ s)

end MaxCut

opaque IsPolyTimeLongCodeReduction {numV numW k numVerts : ℕ} :
    (UniqueGames.UniqueGame (Fin numV) (Fin numW) k → MaxCut.MaxCutInstance (Fin numVerts)) → Prop


noncomputable def maxBalancedNoiseStab (ρ : ℝ) (δ : ℝ) (k : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ (f : (Fin k → Bool) → ℝ),
    (∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) ∧
    (∀ i : Fin k, (1 / (2 : ℝ) ^ k) *
      ∑ x : Fin k → Bool, (f x - f (Function.update x i (!x i))) ^ 2 / 4 ≤ δ) ∧
    ((1 / (2 : ℝ) ^ k) * ∑ x : Fin k → Bool, f x = 0) ∧
    s = (1 / (2 : ℝ) ^ k) * ∑ x : Fin k → Bool, f x *
      ((1 / (2 : ℝ) ^ k) * ∑ y : Fin k → Bool,
        (∏ i : Fin k, if x i = y i then 1 else ρ) * f y)}


noncomputable def longCodeReduce (_ρ : ℝ) (k numV numW : ℕ) :
    UniqueGames.UniqueGame (Fin numV) (Fin numW) k →
    MaxCut.MaxCutInstance (Fin (Fintype.card (Fin numV × (Fin k → Bool)))) := by
  classical
  intro game
  let VType := Fin numV × (Fin k → Bool)
  let eqv : VType ≃ Fin (Fintype.card VType) := Fintype.equivFin VType


  let fwd : Finset (Fin (Fintype.card VType) × Fin (Fintype.card VType)) :=
    game.edges.biUnion fun vw₁ =>
      game.edges.biUnion fun vw₂ =>
        if h : vw₁.2 = vw₂.2 then

          let σ : Equiv.Perm (Fin k) :=
            (game.constraint vw₂.1 vw₂.2).symm.trans (game.constraint vw₁.1 vw₁.2)
          (Finset.univ : Finset (Fin k → Bool)).image fun x =>
            (eqv (vw₁.1, x), eqv (vw₂.1, fun i => !(x (σ.symm i))))
        else ∅
  let bwd := fwd.image (fun p => (p.2, p.1))
  exact ⟨fwd ∪ bwd, by
    intro e he
    simp only [Finset.mem_union] at he ⊢
    rcases he with h | h
    · right; exact Finset.mem_image.mpr ⟨e, h, rfl⟩
    · left
      obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp h
      have heq : e = (p.2, p.1) := hpe.symm
      subst heq; exact hp⟩

