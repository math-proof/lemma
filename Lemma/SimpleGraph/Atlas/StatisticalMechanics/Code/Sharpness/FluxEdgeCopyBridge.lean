import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
open Finset BigOperators StatMech StatMech.Sharpness StatMech.Sharpness.FluxEdgeCopy


/--
[sigmaFinsetEquivPi_apply_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma sigmaFinsetEquivPi_apply_card_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  {S : Finset (Σ e : E, β e)}
  {e : E} :
-- imply
  #(sigmaFinsetEquivPi S e) = #(S.filter (fun i : Σ e, β e => i.1 = e)) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.sigmaFinsetEquivPi_apply_card S e

/--
[pi_card_profile_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma pi_card_profile_count_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  {k : E → ℕ} :
-- imply
  #(univ.filter (fun f : Π e : E, Finset (β e) => (fun e => #(f e)) = k)) = ∏ e : E, (Fintype.card (β e)).choose (k e) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.pi_card_profile_count k

/--
[pi_reindex_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma pi_reindex_profile_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [AddCommMonoid M]
  {Φ : (E → ℕ) → M} :
-- imply
  (∑ f : (Π e : E, Finset (β e)), Φ (fun e => #(f e))) = ∑ k ∈ (univ.image (fun f : Π e : E, Finset (β e) => fun e => #(f e))), (∏ e : E, (Fintype.card (β e)).choose (k e)) • Φ k := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.pi_reindex_profile Φ

/--
[edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma edge_mem_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : V}
-- given
  (hadj : G.Adj a b) :
-- imply
  s(a, b) ∈ G.edgeFinset := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.edge_mem G hadj

/--
[endsM_not_isDiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma endsM_not_isDiag_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Copy G m} :
-- imply
  ¬ (endsM G m i).IsDiag := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.endsM_not_isDiag G m i

/--
[degK_eq_incidentFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma degK_eq_incidentFlux_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {S : Finset (Copy G m)}
  {x : V} :
-- imply
  degK (endsM G m) S x = incidentFlux G (ofEdgeFun G (profileFlux G m S)) x := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.degK_eq_incidentFlux G m S x

/--
[sources_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma sources_eq_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {S : Finset (Copy G m)} :
-- imply
  RandomCurrent.sources (endsM G m) S = sources G (ofEdgeFun G (profileFlux G m S)) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.sources_eq G m S

/--
[adjStep_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma adjStep_iff_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {S : Finset (Copy G m)}
  {a b : V} :
-- imply
  adjStep (endsM G m) S a b ↔ (currentSubgraph G (ofEdgeFun G (profileFlux G m S))).Adj a b := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.adjStep_iff G m S a b

/--
[connK_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma connK_iff_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {S : Finset (Copy G m)}
  {a b : V} :
-- imply
  connK (endsM G m) S a b ↔ CurrentConnected G (ofEdgeFun G (profileFlux G m S)) a b := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.connK_iff G m S a b

/--
[fiber_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma fiber_card_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {e : ↥G.edgeFinset} :
-- imply
  #((univ : Finset (Copy G m)).filter (fun i : Copy G m => i.1 = e)) = m e := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.fiber_card G m e

/--
[profileFlux_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma profileFlux_le_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {S : Finset (Copy G m)} :
-- imply
  profileFlux G m S ≤ m := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.profileFlux_le G m S

/--
[profileFlux_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma profileFlux_compl_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {S : Finset (Copy G m)} :
-- imply
  profileFlux G m (univ \ S) = fun e => m e - profileFlux G m S e := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.profileFlux_compl G m S

/--
[fin_filter_lt_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma fin_filter_lt_card_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n k : ℕ}
-- given
  (h : k ≤ n) :
-- imply
  #((univ : Finset (Fin n)).filter (fun j => j.val < k)) = k := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.fin_filter_lt_card G n k h

/--
[profileFlux_surj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma profileFlux_surj_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {K : ↥G.edgeFinset → ℕ}
-- given
  (hK : K ≤ m) :
-- imply
  profileFlux G m (univ.filter (fun i : Copy G m => i.2.val < K i.1)) = K := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.profileFlux_surj G m K hK

/--
[preimage_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma preimage_count_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {K : ↥G.edgeFinset → ℕ} :
-- imply
  #(univ.filter (fun S : Finset (Copy G m) => profileFlux G m S = K)) = ∏ e : ↥G.edgeFinset, (m e).choose (K e) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.preimage_count G m K

/--
[flux_edgecopy_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma flux_edgecopy_bridge_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [AddCommMonoid M]
  {m : ↥G.edgeFinset → ℕ}
  {Θ : (↥G.edgeFinset → ℕ) → M} :
-- imply
  (∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m}, (∏ e : ↥G.edgeFinset, (m e).choose (K.1 e)) • Θ K.1) = ∑ S : Finset (Copy G m), Θ (profileFlux G m S) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.flux_edgecopy_bridge G m Θ

/--
[sourcePair_superposition_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma sourcePair_superposition_bridge_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {m : ↥G.edgeFinset → ℕ} :
-- imply
  (∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m}, (if sources G (ofEdgeFun G K.1) = A then weight G β J (ofEdgeFun G K.1) else 0) * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B then weight G β J (ofEdgeFun G (fun e => m e - K.1 e)) else 0)) = (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = B then 1 else 0)) * weight G β J (ofEdgeFun G m) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.sourcePair_superposition_bridge G β J A B m

/--
[sourcePairSum_eq_edgecopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma sourcePairSum_eq_edgecopy_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V} :
-- imply
  sourcePairSum G β J A B = ∑' m : ↥G.edgeFinset → ℕ, (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = B then 1 else 0)) * weight G β J (ofEdgeFun G m) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.sourcePairSum_eq_edgecopy G β J A B

/--
[profileFlux_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma profileFlux_univ_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ} :
-- imply
  profileFlux G m (univ : Finset (Copy G m)) = m := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.profileFlux_univ G m

/--
[connK_univ_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma connK_univ_iff_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {u v : V} :
-- imply
  RandomCurrent.connK (endsM G m) univ u v ↔ CurrentConnected G (ofEdgeFun G m) u v := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.connK_univ_iff G m u v

/--
[sourcePair_superposition_bridge_connK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma sourcePair_superposition_bridge_connK_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {m : ↥G.edgeFinset → ℕ}
  {u v : V} :
-- imply
  (∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m}, (if sources G (ofEdgeFun G K.1) = A then weight G β J (ofEdgeFun G K.1) else 0) * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B then weight G β J (ofEdgeFun G (fun e => m e - K.1 e)) else 0) * (if CurrentConnected G (ofEdgeFun G m) u v then (1 : ℝ) else 0)) = (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = B then 1 else 0) * (if RandomCurrent.connK (endsM G m) univ u v then 1 else 0)) * weight G β J (ofEdgeFun G m) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.sourcePair_superposition_bridge_connK G β J A B m u v

/--
[sourcePair_superposition_bridge_disconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma sourcePair_superposition_bridge_disconn_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {m : ↥G.edgeFinset → ℕ}
  {u v : V} :
-- imply
  (∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m}, (if sources G (ofEdgeFun G K.1) = A then weight G β J (ofEdgeFun G K.1) else 0) * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B then weight G β J (ofEdgeFun G (fun e => m e - K.1 e)) else 0) * (if ¬ CurrentConnected G (ofEdgeFun G m) u v then (1 : ℝ) else 0)) = (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = B then 1 else 0) * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0)) * weight G β J (ofEdgeFun G m) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.sourcePair_superposition_bridge_disconn G β J A B m u v

/--
[sourcePairSum_conv_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma sourcePairSum_conv_factor_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {W : (↥G.edgeFinset → ℕ) → ℝ}
-- given
  (hWb : ∀ m, |W m| ≤ 1) :
-- imply
  (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), ((if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0)) * W (fun e => pq.1 e + pq.2 e)) = ∑' m : ↥G.edgeFinset → ℕ, (∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m}, ((if sources G (ofEdgeFun G K.1) = A then weight G β J (ofEdgeFun G K.1) else 0) * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B then weight G β J (ofEdgeFun G (fun e => m e - K.1 e)) else 0))) * W m := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.sourcePairSum_conv_factor G β J A B W hWb

/--
[sourcePairDisconnSum_eq_edgecopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean)
-/
@[path]
private lemma sourcePairDisconnSum_eq_edgecopy_eq
  [Fintype E]
  [DecidableEq E]
  {β : E → Type*}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {u v : V} :
-- imply
  sourcePairDisconnSum G β J A B u v = ∑' m : ↥G.edgeFinset → ℕ, (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = B then 1 else 0) * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0)) * weight G β J (ofEdgeFun G m) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.sourcePairDisconnSum_eq_edgecopy G β J A B u v


-- created on 2026-10-23
