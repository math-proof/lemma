import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.MultiReplica
open Finset BigOperators SimpleGraph StatMech StatMech.Sharpness StatMech.Sharpness.RandomCurrent


/--
[weight_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean)
-/
@[path]
private lemma weight_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n₁ n₂ n₃ : Current V} :
-- imply
  weight G β J n₁ * weight G β J n₂ * weight G β J n₃ = (∏ e ∈ G.edgeFinset, ((Nat.choose (n₁ e + n₂ e + n₃ e) (n₁ e) : ℝ) * (Nat.choose (n₂ e + n₃ e) (n₂ e) : ℝ))) * weight G β J (fun e => n₁ e + n₂ e + n₃ e) := by
-- proof
  apply StatMech.Sharpness.weight_mul G β J n₁ n₂ n₃

/--
[ofEdgeFun_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean)
-/
@[path]
private lemma ofEdgeFun_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q r : ↥G.edgeFinset → ℕ} :
-- imply
  (fun e => (ofEdgeFun G p) e + (ofEdgeFun G q) e + (ofEdgeFun G r) e) = ofEdgeFun G (fun i => p i + q i + r i) := by
-- proof
  apply StatMech.Sharpness.ofEdgeFun_add G p q r

/--
[sources_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean)
-/
@[path]
private lemma sources_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n₁ n₂ n₃ : Current V} :
-- imply
  sources G (fun e => n₁ e + n₂ e + n₃ e) = sources G n₁ ∆ sources G n₂ ∆ sources G n₃ := by
-- proof
  apply StatMech.Sharpness.sources_add G n₁ n₂ n₃

/--
[sources_ofEdgeFun_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean)
-/
@[path]
private lemma sources_ofEdgeFun_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m K₁ K₂ : ↥G.edgeFinset → ℕ}
-- given
  (hK : ∀ e, K₁ e + K₂ e ≤ m e) :
-- imply
  sources G (ofEdgeFun G m) = sources G (ofEdgeFun G K₁) ∆ sources G (ofEdgeFun G K₂) ∆ sources G (ofEdgeFun G (fun e => m e - K₁ e - K₂ e)) := by
-- proof
  apply StatMech.Sharpness.sources_ofEdgeFun_add G m K₁ K₂ hK

/--
[sourceTripleSum_eq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean)
-/
@[path]
private lemma sourceTripleSum_eq_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B C : Finset V} :
-- imply
  sourceTripleSum G β J A B C = currentSum G β J A * currentSum G β J B * currentSum G β J C := by
-- proof
  apply StatMech.Sharpness.sourceTripleSum_eq_mul G β J A B C

/--
[sourceTripleSum_eq_superposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean)
-/
@[path]
private lemma sourceTripleSum_eq_superposition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B C : Finset V} :
-- imply
  sourceTripleSum G β J A B C = ∑' m : ↥G.edgeFinset → ℕ, ∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}, (if sources G (ofEdgeFun G K.1.1) = A then weight G β J (ofEdgeFun G K.1.1) else 0) * (if sources G (ofEdgeFun G K.1.2) = B then weight G β J (ofEdgeFun G K.1.2) else 0) * (if sources G (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) = C then weight G β J (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) else 0) := by
-- proof
  apply StatMech.Sharpness.sourceTripleSum_eq_superposition G β J A B C

/--
[sourceTripleSum_superposition_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean)
-/
@[path]
private lemma sourceTripleSum_superposition_source_eq
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
  apply StatMech.Sharpness.sourceTripleSum_superposition_source G m K₁ K₂ hK hA hB hC

/--
[weight_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean)
-/
@[path]
private lemma weight_split_eq
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
  apply StatMech.Sharpness.weight_split G β J m K₁ K₂ hK

/--
[sources_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean)
-/
@[path]
private lemma sources_shift_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m P Q : Finset ι}
  {A : Finset W}
-- given
  (hP : P ⊆ m)
  (hQ : Q ⊆ m) :
-- imply
  Set.BijOn (fun K => (K ∆ P) ∆ Q) {K | K ⊆ m ∧ sources ends K = A} {K | K ⊆ m ∧ sources ends K = A ∆ sources ends P ∆ sources ends Q} := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.sources_shift G ends m P Q hP hQ A

/--
[switching_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean)
-/
@[path]
private lemma switching_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {A : Finset W}
  {u v s t : W}
-- given
  (huv : u ≠ v)
  (hst : s ≠ t)
  (hconnuv : connK ends m u v)
  (hconnst : connK ends m s t) :
-- imply
  #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {s, t})) = #(m.powerset.filter (fun K => sources ends K = A)) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.switching_card G ends m A huv hst hconnuv hconnst

/--
[switching_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean)
-/
@[path]
private lemma switching_lemma_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {A : Finset W}
  {u v s t : W}
  {F : Finset ι → ℝ}
-- given
  (huv : u ≠ v)
  (hst : s ≠ t)
  (hconnuv : connK ends m u v)
  (hconnst : connK ends m s t) :
-- imply
  ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {s, t}), F m = ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A), F m := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.switching_lemma G ends m A huv hst hconnuv hconnst F


-- created on 2026-10-23
