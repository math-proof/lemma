import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.ClaimIsingFull
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[reach_restrictCompl_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma reach_restrictCompl_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {S : Finset V}
  {u v : V}
-- given
  (hr : (currentSubgraph G (restrictTo m Sᶜ)).Reachable u v) :
-- imply
  (currentSubgraph G m).Reachable u v := by
-- proof
  apply StatMech.Sharpness.reach_restrictCompl_le G m S hr

/--
[reach_forward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma reach_forward_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {S : Finset V}
  {u v : V}
-- given
  (hn : NoCrossing G m S)
  (hu : u ∉ S)
  (hr : (currentSubgraph G m).Reachable u v) :
-- imply
  (currentSubgraph G (restrictTo m Sᶜ)).Reachable u v ∧ v ∉ S := by
-- proof
  apply StatMech.Sharpness.reach_forward G m S hn u v hu hr

/--
[currentConnected_iff_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma currentConnected_iff_compl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {S : Finset V}
  {u v : V}
-- given
  (hn : NoCrossing G m S)
  (hu : u ∉ S) :
-- imply
  CurrentConnected G m u v ↔ CurrentConnected G (restrictTo m Sᶜ) u v := by
-- proof
  apply StatMech.Sharpness.currentConnected_iff_compl G m S hn u v hu

/--
[not_currentConnected_in_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma not_currentConnected_in_S_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {S : Finset V}
  {g : V}
  {v : V}
-- given
  (hn : NoCrossing G m S)
  (hg : g ∉ S)
  (hv : v ∈ S) :
-- imply
  ¬ CurrentConnected G m g v := by
-- proof
  apply StatMech.Sharpness.not_currentConnected_in_S G m S hn g hg v hv

/--
[aFull_notIn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma aFull_notIn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  (a)
  {i : ↥G.edgeFinset}
-- given
  (hi : ¬ isIn G S i) :
-- imply
  aFull G S a i = 0 := by
-- proof
  apply StatMech.Sharpness.aFull_notIn G S i hi

/--
[reEdge_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma reEdge_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  (ab)
  {i : ↥G.edgeFinset} :
-- imply
  reEdge G S ab i = if h : isIn G S i then ab.1 ⟨i, h⟩ else ab.2 ⟨i, h⟩ := by
-- proof
  apply StatMech.Sharpness.reEdge_apply G S i

/--
[reEdge_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma reEdge_zero_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  (a) :
-- imply
  reEdge G S (a, fun _ => 0) = aFull G S a := by
-- proof
  apply StatMech.Sharpness.reEdge_zero_right G S

/--
[reEdge_eq_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma reEdge_eq_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  (a b)
  {i : ↥G.edgeFinset} :
-- imply
  reEdge G S (a, b) i = aFull G S a i + bFull G S b i := by
-- proof
  apply StatMech.Sharpness.reEdge_eq_add G S i

/--
[ofEdgeFun_reEdge_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma ofEdgeFun_reEdge_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  (a b) :
-- imply
  (fun e => (ofEdgeFun G (aFull G S a)) e + (ofEdgeFun G (bFull G S b)) e) = ofEdgeFun G (reEdge G S (a, b)) := by
-- proof
  apply StatMech.Sharpness.ofEdgeFun_reEdge_add G S

/--
[aFull_bFull_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma aFull_bFull_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  (a b)
  {e : Sym2 V} :
-- imply
  (ofEdgeFun G (aFull G S a)) e = 0 ∨ (ofEdgeFun G (bFull G S b)) e = 0 := by
-- proof
  apply StatMech.Sharpness.aFull_bFull_disjoint G S e

/--
[weight_reEdge_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma weight_reEdge_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  (a b) :
-- imply
  weight G β J (ofEdgeFun G (reEdge G S (a, b))) = weight G β J (ofEdgeFun G (aFull G S a)) * weight G β J (ofEdgeFun G (bFull G S b)) := by
-- proof
  apply StatMech.Sharpness.weight_reEdge_split G β J S

/--
[sources_reEdge_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma sources_reEdge_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  (a b) :
-- imply
  sources G (ofEdgeFun G (reEdge G S (a, b))) = sources G (ofEdgeFun G (aFull G S a)) ∆ sources G (ofEdgeFun G (bFull G S b)) := by
-- proof
  apply StatMech.Sharpness.sources_reEdge_split G S

/--
[incidentFlux_aFull_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma incidentFlux_aFull_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  (a)
  {v : V}
-- given
  (hv : v ∉ S) :
-- imply
  incidentFlux G (ofEdgeFun G (aFull G S a)) v = 0 := by
-- proof
  apply StatMech.Sharpness.incidentFlux_aFull_zero G S hv

/--
[sources_aFull_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma sources_aFull_subset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  (a) :
-- imply
  sources G (ofEdgeFun G (aFull G S a)) ⊆ S := by
-- proof
  apply StatMech.Sharpness.sources_aFull_subset G S

/--
[incidentFlux_bFull_zero_of_noCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma incidentFlux_bFull_zero_of_noCross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  (b)
  {v : V}
-- given
  (hcross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S b i → edgeInside Sᶜ (i : Sym2 V))
  (hv : v ∈ S) :
-- imply
  incidentFlux G (ofEdgeFun G (bFull G S b)) v = 0 := by
-- proof
  apply StatMech.Sharpness.incidentFlux_bFull_zero_of_noCross G S hcross hv

/--
[sources_bFull_subset_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma sources_bFull_subset_compl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  (b)
-- given
  (hcross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S b i → edgeInside Sᶜ (i : Sym2 V)) :
-- imply
  sources G (ofEdgeFun G (bFull G S b)) ⊆ Sᶜ := by
-- proof
  apply StatMech.Sharpness.sources_bFull_subset_compl G S hcross

/--
[weight_couplingIn_aFull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma weight_couplingIn_aFull_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  (a) :
-- imply
  weight G β (couplingIn J S) (ofEdgeFun G (aFull G S a)) = weight G β J (ofEdgeFun G (aFull G S a)) := by
-- proof
  apply StatMech.Sharpness.weight_couplingIn_aFull G β J S

/--
[weight_reEdge_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma weight_reEdge_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  (a)
  {b : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ}
  {j : {i : ↥G.edgeFinset // ¬ isIn G S i}}
-- given
  (hj : 1 ≤ b j) :
-- imply
  weight G β (couplingIn J S) (ofEdgeFun G (reEdge G S (a, b))) = 0 := by
-- proof
  apply StatMech.Sharpness.weight_reEdge_eq_zero G β J S b j hj

/--
[currentSum_couplingIn_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma currentSum_couplingIn_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {A : Finset V} :
-- imply
  currentSum G β (couplingIn J S) A = ∑' a : {i : ↥G.edgeFinset // isIn G S i} → ℕ, (if sources G (ofEdgeFun G (aFull G S a)) = A then weight G β J (ofEdgeFun G (aFull G S a)) else 0) := by
-- proof
  apply StatMech.Sharpness.currentSum_couplingIn_eq G β J S A

/--
[aFull_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma aFull_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V} :
-- imply
  Function.Injective (aFull G S) := by
-- proof
  apply StatMech.Sharpness.aFull_injective G S

/--
[bFull_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma bFull_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V} :
-- imply
  Function.Injective (bFull G S) := by
-- proof
  apply StatMech.Sharpness.bFull_injective G S

/--
[summable_norm_weight_aFull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma summable_norm_weight_aFull_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V} :
-- imply
  Summable (fun a : {i : ↥G.edgeFinset // isIn G S i} → ℕ => ‖weight G β J (ofEdgeFun G (aFull G S a))‖) := by
-- proof
  apply StatMech.Sharpness.summable_norm_weight_aFull G β J S

/--
[summable_norm_weight_bFull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma summable_norm_weight_bFull_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V} :
-- imply
  Summable (fun b : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ => ‖weight G β J (ofEdgeFun G (bFull G S b))‖) := by
-- proof
  apply StatMech.Sharpness.summable_norm_weight_bFull G β J S

/--
[summand_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma summand_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  [DecidablePred P]
  {A : Finset V}
  {a : {i : ↥G.edgeFinset // isIn G S i} → ℕ}
  {b : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ}
  {n₂ : ↥G.edgeFinset → ℕ}
-- given
  (P : Current V → Prop)
  (H1 : ∀ m, P m → NoCrossing G m S)
  (H2 : ∀ m m' : Current V, (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
  (hAS : A ⊆ S) :
-- imply
  (if sources G (ofEdgeFun G (reEdge G S (a, b))) = A then weight G β J (ofEdgeFun G (reEdge G S (a, b))) else 0) * (if sources G (ofEdgeFun G n₂) = ∅ then weight G β J (ofEdgeFun G n₂) else 0) * (if P (fun e => ofEdgeFun G (reEdge G S (a, b)) e + ofEdgeFun G n₂ e) then 1 else 0) = (if sources G (ofEdgeFun G (aFull G S a)) = A then weight G β J (ofEdgeFun G (aFull G S a)) else 0) * ((if sources G (ofEdgeFun G (bFull G S b)) = ∅ then weight G β J (ofEdgeFun G (bFull G S b)) else 0) * (if sources G (ofEdgeFun G n₂) = ∅ then weight G β J (ofEdgeFun G n₂) else 0) * (if P (fun e => ofEdgeFun G (bFull G S b) e + ofEdgeFun G n₂ e) then 1 else 0)) := by
-- proof
  apply StatMech.Sharpness.summand_factor G β J S P H1 H2 A hAS a b n₂

/--
[norm_factorSummand_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma norm_factorSummand_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {A : Finset V}
  {a : {i : ↥G.edgeFinset // isIn G S i} → ℕ} :
-- imply
  ‖factorSummand G β J S A a‖ ≤ ‖weight G β J (ofEdgeFun G (aFull G S a))‖ := by
-- proof
  apply StatMech.Sharpness.norm_factorSummand_le G β J S A a

/--
[summable_factorSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma summable_factorSummand_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {A : Finset V} :
-- imply
  Summable (factorSummand G β J S A) := by
-- proof
  apply StatMech.Sharpness.summable_factorSummand G β J S A

/--
[norm_triple_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma norm_triple_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w₁ w₂ : ℝ}
  [Decidable P₁]
  [Decidable P₂]
  [Decidable P₃]
-- given
  (P₁ P₂ P₃ : Prop) :
-- imply
  ‖(if P₁ then w₁ else 0) * (if P₂ then w₂ else 0) * (if P₃ then (1 : ℝ) else 0)‖ ≤ ‖w₁‖ * ‖w₂‖ := by
-- proof
  apply StatMech.Sharpness.norm_triple_le G w₁ w₂ P₁ P₂ P₃

/--
[norm_contextSummand_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma norm_contextSummand_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  [DecidablePred P]
  {bn : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ)}
-- given
  (P : Current V → Prop) :
-- imply
  ‖contextSummand G β J S P bn‖ ≤ ‖weight G β J (ofEdgeFun G (bFull G S bn.1))‖ * ‖weight G β J (ofEdgeFun G bn.2)‖ := by
-- proof
  apply StatMech.Sharpness.norm_contextSummand_le G β J S P bn

/--
[summable_contextSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma summable_contextSummand_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  [DecidablePred P]
-- given
  (P : Current V → Prop) :
-- imply
  Summable (contextSummand G β J S P) := by
-- proof
  apply StatMech.Sharpness.summable_contextSummand G β J S P

/--
[summable_factor_context](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma summable_factor_context_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {A : Finset V}
  [DecidablePred P]
-- given
  (P : Current V → Prop) :
-- imply
  Summable (fun abn : ({i : ↥G.edgeFinset // isIn G S i} → ℕ) × (({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ)) => factorSummand G β J S A abn.1 * contextSummand G β J S P abn.2) := by
-- proof
  apply StatMech.Sharpness.summable_factor_context G β J S A P

/--
[claim2_pairSum_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma claim2_pairSum_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  [DecidablePred P]
  {A : Finset V}
-- given
  (P : Current V → Prop)
  (H1 : ∀ m, P m → NoCrossing G m S)
  (H2 : ∀ m m' : Current V, (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
  (hAS : A ⊆ S) :
-- imply
  (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0) * (if P (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) then 1 else 0)) = currentSum G β (couplingIn J S) A * (∑' bn : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ), contextSummand G β J S P bn) := by
-- proof
  apply StatMech.Sharpness.claim2_pairSum_factor G β J S P H1 H2 A hAS

/--
[claim2_abstract](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma claim2_abstract_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  [DecidablePred P]
  {zero x : V}
-- given
  (P : Current V → Prop)
  (H1 : ∀ m, P m → NoCrossing G m S)
  (H2 : ∀ m m' : Current V, (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
  (h0 : zero ∈ S)
  (hx : x ∈ S)
  (hZ : currentSum G β (couplingIn J S) ∅ ≠ 0) :
-- imply
  (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if sources G (ofEdgeFun G pq.1) = {zero, x} then weight G β J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0) * (if P (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) then 1 else 0)) = expectationJ G β (couplingIn J S) {zero, x} * (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0) * (if P (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) then 1 else 0)) := by
-- proof
  apply StatMech.Sharpness.claim2_abstract G β J S P H1 H2 zero x h0 hx hZ

/--
[mem_notConnComp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma mem_notConnComp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {g v : V} :
-- imply
  v ∈ notConnComp G m g ↔ ¬ CurrentConnected G m g v := by
-- proof
  apply StatMech.Sharpness.mem_notConnComp G

/--
[noCrossing_of_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma noCrossing_of_event_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {S : Finset V}
  {g : V}
-- given
  (_hg : g ∉ S)
  (hev : notConnComp G m g = S) :
-- imply
  NoCrossing G m S := by
-- proof
  apply StatMech.Sharpness.noCrossing_of_event G m S g _hg hev

/--
[currentSubgraph_restrictCompl_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma currentSubgraph_restrictCompl_congr_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m m' : Current V}
  {S : Finset V}
-- given
  (hagree : ∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) :
-- imply
  currentSubgraph G (restrictTo m Sᶜ) = currentSubgraph G (restrictTo m' Sᶜ) := by
-- proof
  apply StatMech.Sharpness.currentSubgraph_restrictCompl_congr G m m' S hagree

/--
[noCrossing_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma noCrossing_congr_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m m' : Current V}
  {S : Finset V}
-- given
  (hnm : NoCrossing G m S)
  (hagree : ∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) :
-- imply
  NoCrossing G m' S := by
-- proof
  apply StatMech.Sharpness.noCrossing_congr G m m' S hnm hagree

/--
[notConnComp_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma notConnComp_congr_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m m' : Current V}
  {S : Finset V}
  {g : V}
-- given
  (hg : g ∉ S)
  (hev : notConnComp G m g = S)
  (hagree : ∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) :
-- imply
  notConnComp G m' g = S := by
-- proof
  apply StatMech.Sharpness.notConnComp_congr G m m' S g hg hev hagree

/--
[claim2_ising](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean)
-/
@[path]
private lemma claim2_ising_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {g : V}
  {zero x : V}
-- given
  (hg : g ∉ S)
  (h0 : zero ∈ S)
  (hx : x ∈ S)
  (hZ : currentSum G β (couplingIn J S) ∅ ≠ 0) :
-- imply
  (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if sources G (ofEdgeFun G pq.1) = {zero, x} then weight G β J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0) * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S then 1 else 0)) = expectationJ G β (couplingIn J S) {zero, x} * (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0) * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S then 1 else 0)) := by
-- proof
  apply StatMech.Sharpness.claim2_ising G β J S g hg zero x h0 hx hZ


-- created on 2026-10-23
