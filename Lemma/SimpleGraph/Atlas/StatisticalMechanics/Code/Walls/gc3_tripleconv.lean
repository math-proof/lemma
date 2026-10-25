import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc3_tripleconv
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc3_sourceTripleSum_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_tripleconv.lean)
-/
@[path]
private lemma gc3_sourceTripleSum_def_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B C : Finset V} :
-- imply
  gc3_sourceTripleSum G β J A B C = ∑' z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if sources G (ofEdgeFun G z.1) = A then weight G β J (ofEdgeFun G z.1) else 0) * (if sources G (ofEdgeFun G z.2.1) = B then weight G β J (ofEdgeFun G z.2.1) else 0) * (if sources G (ofEdgeFun G z.2.2) = C then weight G β J (ofEdgeFun G z.2.2) else 0) := by
-- proof
  apply StatMech.Walls.gc3_sourceTripleSum_def G β J A B C

/--
[gc3_sourceTripleSum_eq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_tripleconv.lean)
-/
@[path]
private lemma gc3_sourceTripleSum_eq_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B C : Finset V} :
-- imply
  gc3_sourceTripleSum G β J A B C = currentSum G β J A * currentSum G β J B * currentSum G β J C := by
-- proof
  apply StatMech.Walls.gc3_sourceTripleSum_eq_mul G β J A B C

/--
[gc3_tripleConv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_tripleconv.lean)
-/
@[path]
private lemma gc3_tripleConv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B C : Finset V} :
-- imply
  gc3_sourceTripleSum G β J A B C = ∑' m : ↥G.edgeFinset → ℕ, ∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}, (if sources G (ofEdgeFun G K.1.1) = A then weight G β J (ofEdgeFun G K.1.1) else 0) * (if sources G (ofEdgeFun G K.1.2) = B then weight G β J (ofEdgeFun G K.1.2) else 0) * (if sources G (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) = C then weight G β J (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) else 0) := by
-- proof
  apply StatMech.Walls.gc3_tripleConv G β J A B C

/--
[gc3_tripleConv_superposition_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_tripleconv.lean)
-/
@[path]
private lemma gc3_tripleConv_superposition_source_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m K₁ K₂ : ↥G.edgeFinset → ℕ}
  {A B C : Finset V}
-- given
  (hK : ∀ e, K₁ e + K₂ e ≤ m e)
  (hA : sources G (ofEdgeFun G K₁) = A)
  (hB : sources G (ofEdgeFun G K₂) = B)
  (hC : sources G (ofEdgeFun G (fun e => m e - K₁ e - K₂ e)) = C) :
-- imply
  sources G (ofEdgeFun G m) = A ∆ B ∆ C := by
-- proof
  apply StatMech.Walls.gc3_tripleConv_superposition_source G m K₁ K₂ hK hA hB hC

/--
[gc3_tripleConv_weight_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_tripleconv.lean)
-/
@[path]
private lemma gc3_tripleConv_weight_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m K₁ K₂ : ↥G.edgeFinset → ℕ}
-- given
  (hK : ∀ e, K₁ e + K₂ e ≤ m e) :
-- imply
  weight G β J (ofEdgeFun G K₁) * weight G β J (ofEdgeFun G K₂) * weight G β J (ofEdgeFun G (fun e => m e - K₁ e - K₂ e)) = (∏ e ∈ G.edgeFinset, ((Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K₁) e) : ℝ) * (Nat.choose ((ofEdgeFun G m) e - (ofEdgeFun G K₁) e) ((ofEdgeFun G K₂) e) : ℝ))) * weight G β J (ofEdgeFun G m) := by
-- proof
  apply StatMech.Walls.gc3_tripleConv_weight_split G β J m K₁ K₂ hK

/--
[gc3_tripleConv_pinned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_tripleconv.lean)
-/
@[path]
private lemma gc3_tripleConv_pinned_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B C : Finset V} :
-- imply
  gc3_sourceTripleSum G β J A B C = ∑' m : ↥G.edgeFinset → ℕ, (if sources G (ofEdgeFun G m) = A ∆ B ∆ C then (1 : ℝ) else 0) * ∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}, (if sources G (ofEdgeFun G K.1.1) = A then weight G β J (ofEdgeFun G K.1.1) else 0) * (if sources G (ofEdgeFun G K.1.2) = B then weight G β J (ofEdgeFun G K.1.2) else 0) * (if sources G (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) = C then weight G β J (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) else 0) := by
-- proof
  apply StatMech.Walls.gc3_tripleConv_pinned G β J A B C


-- created on 2026-10-23
