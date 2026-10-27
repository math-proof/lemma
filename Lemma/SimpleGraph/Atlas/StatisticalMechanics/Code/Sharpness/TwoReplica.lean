import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
open Finset BigOperators SimpleGraph StatMech StatMech.Sharpness


/--
[weight_mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TwoReplica.lean)
-/
@[path]
private lemma weight_mul_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n₁ n₂ : Current V} :
-- imply
  weight G β J n₁ * weight G β J n₂ = (∏ e ∈ G.edgeFinset, (Nat.choose (n₁ e + n₂ e) (n₁ e) : ℝ)) * weight G β J (fun e => n₁ e + n₂ e) := by
-- proof
  apply StatMech.Sharpness.weight_mul_eq G β J n₁ n₂

/--
[ofEdgeFun_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TwoReplica.lean)
-/
@[path]
private lemma ofEdgeFun_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ↥G.edgeFinset → ℕ} :
-- imply
  (fun e => (ofEdgeFun G p) e + (ofEdgeFun G q) e) = ofEdgeFun G (fun i => p i + q i) := by
-- proof
  apply StatMech.Sharpness.ofEdgeFun_add G p q

/--
[sources_ofEdgeFun_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TwoReplica.lean)
-/
@[path]
private lemma sources_ofEdgeFun_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m K : ↥G.edgeFinset → ℕ}
-- given
  (hK : K ≤ m) :
-- imply
  sources G (ofEdgeFun G m) = sources G (ofEdgeFun G K) ∆ sources G (ofEdgeFun G (fun e => m e - K e)) := by
-- proof
  apply StatMech.Sharpness.sources_ofEdgeFun_add G m K hK

/--
[summable_norm_wEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TwoReplica.lean)
-/
@[path]
private lemma summable_norm_wEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {e : Sym2 V} :
-- imply
  Summable (fun k => ‖wEdge β J e k‖) := by
-- proof
  apply StatMech.Sharpness.summable_norm_wEdge G β J e

/--
[summable_norm_weight_ofEdgeFun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TwoReplica.lean)
-/
@[path]
private lemma summable_norm_weight_ofEdgeFun_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  Summable (fun m : ↥G.edgeFinset → ℕ => ‖weight G β J (ofEdgeFun G m)‖) := by
-- proof
  apply StatMech.Sharpness.summable_norm_weight_ofEdgeFun G β J

/--
[summable_norm_currentSum_summand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TwoReplica.lean)
-/
@[path]
private lemma summable_norm_currentSum_summand_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  Summable (fun m : ↥G.edgeFinset → ℕ => ‖if sources G (ofEdgeFun G m) = A then weight G β J (ofEdgeFun G m) else 0‖) := by
-- proof
  apply StatMech.Sharpness.summable_norm_currentSum_summand G β J A

/--
[sourcePairSum_eq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TwoReplica.lean)
-/
@[path]
private lemma sourcePairSum_eq_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V} :
-- imply
  sourcePairSum G β J A B = currentSum G β J A * currentSum G β J B := by
-- proof
  apply StatMech.Sharpness.sourcePairSum_eq_mul G β J A B

/--
[sourcePairSum_eq_superposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TwoReplica.lean)
-/
@[path]
private lemma sourcePairSum_eq_superposition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V} :
-- imply
  sourcePairSum G β J A B = ∑' m : ↥G.edgeFinset → ℕ, ∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m}, (if sources G (ofEdgeFun G K.1) = A then weight G β J (ofEdgeFun G K.1) else 0) * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B then weight G β J (ofEdgeFun G (fun e => m e - K.1 e)) else 0) := by
-- proof
  apply StatMech.Sharpness.sourcePairSum_eq_superposition G β J A B

/--
[sourcePairSum_superposition_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TwoReplica.lean)
-/
@[path]
private lemma sourcePairSum_superposition_source_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m K : ↥G.edgeFinset → ℕ}
  {A B : Finset V}
-- given
  (hK : K ≤ m)
  (hA : sources G (ofEdgeFun G K) = A)
  (hB : sources G (ofEdgeFun G (fun e => m e - K e)) = B) :
-- imply
  sources G (ofEdgeFun G m) = A ∆ B := by
-- proof
  apply StatMech.Sharpness.sourcePairSum_superposition_source G m K hK hA hB

/--
[weight_split_eq_binom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TwoReplica.lean)
-/
@[path]
private lemma weight_split_eq_binom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m K : ↥G.edgeFinset → ℕ}
-- given
  (hK : K ≤ m) :
-- imply
  weight G β J (ofEdgeFun G K) * weight G β J (ofEdgeFun G (fun e => m e - K e)) = (∏ e ∈ G.edgeFinset, (Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K) e) : ℝ)) * weight G β J (ofEdgeFun G m) := by
-- proof
  apply StatMech.Sharpness.weight_split_eq_binom G β J m K hK


-- created on 2026-10-23
