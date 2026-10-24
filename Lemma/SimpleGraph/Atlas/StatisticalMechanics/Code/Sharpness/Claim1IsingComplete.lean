import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete
open SimpleGraph Finset Classical StatMech StatMech.Sharpness StatMech.Sharpness.FluxEdgeCopy


/--
[symmDiff_eq_symmDiff_iff_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma symmDiff_eq_symmDiff_iff_of_separated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S X Y A B : Finset V}
-- given
  (hXS : X ⊆ S)
  (hYS : Y ⊆ Sᶜ)
  (hAS : A ⊆ S)
  (hBS : B ⊆ Sᶜ) :
-- imply
  X ∆ Y = A ∆ B ↔ X = A ∧ Y = B := by
-- proof
  apply StatMech.Sharpness.symmDiff_eq_symmDiff_iff_of_separated G S X Y A B hXS hYS hAS hBS

/--
[sources_reEdge_eq_symmDiff_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma sources_reEdge_eq_symmDiff_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S A B : Finset V}
  {a : {i : ↥G.edgeFinset // isIn G S i} → ℕ}
  {b : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ}
-- given
  (hAS : A ⊆ S)
  (hBS : B ⊆ Sᶜ)
  (hcross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S b i → edgeInside Sᶜ (i : Sym2 V)) :
-- imply
  sources G (ofEdgeFun G (reEdge G S (a, b))) = A ∆ B ↔ sources G (ofEdgeFun G (aFull G S a)) = A ∧ sources G (ofEdgeFun G (bFull G S b)) = B := by
-- proof
  apply StatMech.Sharpness.sources_reEdge_eq_symmDiff_iff G S A B hAS hBS a b hcross

/--
[claim1_summand_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma claim1_summand_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  [DecidablePred P]
  {A B C D : Finset V}
  {a c : {i : ↥G.edgeFinset // isIn G S i} → ℕ}
  {b d : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ}
-- given
  (P : Current V → Prop)
  (H1 : ∀ m, P m → NoCrossing G m S)
  (H2 : ∀ m m' : Current V, (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
  (hAS : A ⊆ S)
  (hBS : B ⊆ Sᶜ)
  (hCS : C ⊆ S)
  (hDS : D ⊆ Sᶜ) :
-- imply
  (if sources G (ofEdgeFun G (reEdge G S (a, b))) = A ∆ B then weight G β J (ofEdgeFun G (reEdge G S (a, b))) else 0) * (if sources G (ofEdgeFun G (reEdge G S (c, d))) = C ∆ D then weight G β J (ofEdgeFun G (reEdge G S (c, d))) else 0) * (if P (fun e => ofEdgeFun G (reEdge G S (a, b)) e + ofEdgeFun G (reEdge G S (c, d)) e) then 1 else 0) = factorSummand G β J S A a * factorSummand G β J S C c * claim1Context G β J S P B D (b, d) := by
-- proof
  apply StatMech.Sharpness.claim1_summand_factor G β J S P H1 H2 A B C D hAS hBS hCS hDS a c b d

/--
[norm_claim1Context_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma norm_claim1Context_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  [DecidablePred P]
  {B D : Finset V}
  {bd : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)}
-- given
  (P : Current V → Prop) :
-- imply
  ‖claim1Context G β J S P B D bd‖ ≤ ‖weight G β J (ofEdgeFun G (bFull G S bd.1))‖ * ‖weight G β J (ofEdgeFun G (bFull G S bd.2))‖ := by
-- proof
  apply StatMech.Sharpness.norm_claim1Context_le G β J S P B D bd

/--
[summable_claim1Context](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma summable_claim1Context_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  [DecidablePred P]
  {B D : Finset V}
-- given
  (P : Current V → Prop) :
-- imply
  Summable (claim1Context G β J S P B D) := by
-- proof
  apply StatMech.Sharpness.summable_claim1Context G β J S P B D

/--
[summable_claim1Interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma summable_claim1Interior_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {A C : Finset V} :
-- imply
  Summable (fun ac : ({i : ↥G.edgeFinset // isIn G S i} → ℕ) × ({i : ↥G.edgeFinset // isIn G S i} → ℕ) => factorSummand G β J S A ac.1 * factorSummand G β J S C ac.2) := by
-- proof
  apply StatMech.Sharpness.summable_claim1Interior G β J S A C

/--
[claim1_pairSum_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma claim1_pairSum_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  [DecidablePred P]
  {A B C D : Finset V}
-- given
  (P : Current V → Prop)
  (H1 : ∀ m, P m → NoCrossing G m S)
  (H2 : ∀ m m' : Current V, (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
  (hAS : A ⊆ S)
  (hBS : B ⊆ Sᶜ)
  (hCS : C ⊆ S)
  (hDS : D ⊆ Sᶜ) :
-- imply
  (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if sources G (ofEdgeFun G pq.1) = A ∆ B then weight G β J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = C ∆ D then weight G β J (ofEdgeFun G pq.2) else 0) * (if P (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) then 1 else 0)) = currentSum G β (couplingIn J S) A * currentSum G β (couplingIn J S) C * (∑' bd, claim1Context G β J S P B D bd) := by
-- proof
  apply StatMech.Sharpness.claim1_pairSum_factor G β J S P H1 H2 A B C D hAS hBS hCS hDS

/--
[sources_univ_eq_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma sources_univ_eq_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {K : Finset (Copy G m)} :
-- imply
  RandomCurrent.sources (endsM G m) (univ : Finset (Copy G m)) = RandomCurrent.sources (endsM G m) K ∆ RandomCurrent.sources (endsM G m) ((univ : Finset (Copy G m)) \ K) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.sources_univ_eq_symmDiff G m K

/--
[edgecopy_sourcePair_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma edgecopy_sourcePair_switching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {A : Finset V}
  {u v : V}
-- given
  (huv : u ≠ v) :
-- imply
  (∑ K : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) K = A ∆ {u, v} then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) ((univ : Finset (Copy G m)) \ K) = {u, v} then 1 else 0)) = ∑ K : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) K = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) ((univ : Finset (Copy G m)) \ K) = ∅ then 1 else 0) * (if RandomCurrent.connK (endsM G m) univ u v then 1 else 0) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.edgecopy_sourcePair_switching G m A huv

/--
[gatedSourcePairSum_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma gatedSourcePairSum_switching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
  [DecidablePred P]
-- given
  (huv : u ≠ v)
  (P : Current V → Prop) :
-- imply
  gatedSourcePairSum G β J (A ∆ {u, v}) {u, v} P = gatedSourcePairSum G β J A ∅ (fun m => P m ∧ CurrentConnected G m u v) := by
-- proof
  apply StatMech.Sharpness.gatedSourcePairSum_switching G β J A huv P

/--
[expectationJ_eq_expJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma expectationJ_eq_expJ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  expectationJ G β J A = expJ G.edgeFinset (fun e => β * J e) (fun _ => 0) (Ising.spinProd A) := by
-- proof
  apply StatMech.Sharpness.expectationJ_eq_expJ G β J A

/--
[expectationJ_couplingIn_eq_expJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma expectationJ_couplingIn_eq_expJ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S A : Finset V} :
-- imply
  expectationJ G β (couplingIn J S) A = expJ (edgesIn G S) (fun e => β * J e) (fun _ => 0) (Ising.spinProd A) := by
-- proof
  apply StatMech.Sharpness.expectationJ_couplingIn_eq_expJ G β J S A

/--
[expectationJ_couplingIn_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma expectationJ_couplingIn_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S A : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  expectationJ G β (couplingIn J S) A ≤ expectationJ G β J A := by
-- proof
  apply StatMech.Sharpness.expectationJ_couplingIn_le G β J hβ hJ S A

/--
[gatedSourcePairSum_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma gatedSourcePairSum_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  [DecidablePred P]
  {A B C D : Finset V}
-- given
  (P : Current V → Prop)
  (H1 : ∀ m, P m → NoCrossing G m S)
  (H2 : ∀ m m' : Current V, (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
  (hAS : A ⊆ S)
  (hBS : B ⊆ Sᶜ)
  (hCS : C ⊆ S)
  (hDS : D ⊆ Sᶜ) :
-- imply
  gatedSourcePairSum G β J (A ∆ B) (C ∆ D) P = currentSum G β (couplingIn J S) A * currentSum G β (couplingIn J S) C * (∑' bd, claim1Context G β J S P B D bd) := by
-- proof
  apply StatMech.Sharpness.gatedSourcePairSum_factor G β J S P H1 H2 A B C D hAS hBS hCS hDS

/--
[claim1Context_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma claim1Context_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  [DecidablePred P]
  {B D : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (P : Current V → Prop) :
-- imply
  0 ≤ ∑' bd, claim1Context G β J S P B D bd := by
-- proof
  apply StatMech.Sharpness.claim1Context_nonneg G β J hβ hJ S P B D

/--
[claim1_ising_cleared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma claim1_ising_cleared_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {o x y g : V}
  {mΛ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (ho : o ∉ S)
  (hx : x ∉ S)
  (hy : y ∈ S)
  (hg : g ∈ S)
  (hyg : y ≠ g)
  (hgriff : expectationJ G β (couplingIn J S) {y, g} ≤ mΛ) :
-- imply
  mΛ * gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅ (fun m => notConnComp G m o = S) ≥ gatedSourcePairSum G β J {o, x} ∅ (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) := by
-- proof
  apply StatMech.Sharpness.claim1_ising_cleared G β J hβ hJ S o x y g ho hx hy hg hyg mΛ hgriff

/--
[claim1_ising](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma claim1_ising_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {o x y g : V}
  {mΛ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (ho : o ∉ S)
  (hx : x ∉ S)
  (hy : y ∈ S)
  (hg : g ∈ S)
  (hyg : y ≠ g)
  (hmΛ : 0 < mΛ)
  (hgriff : expectationJ G β (couplingIn J S) {y, g} ≤ mΛ) :
-- imply
  gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅ (fun m => notConnComp G m o = S) ≥ mΛ⁻¹ * gatedSourcePairSum G β J {o, x} ∅ (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) := by
-- proof
  apply StatMech.Sharpness.claim1_ising G β J hβ hJ S o x y g ho hx hy hg hyg mΛ hmΛ hgriff

/--
[claim1_ising_unconditional_cleared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma claim1_ising_unconditional_cleared_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {o x y g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (ho : o ∉ S)
  (hx : x ∉ S)
  (hy : y ∈ S)
  (hg : g ∈ S)
  (hyg : y ≠ g) :
-- imply
  expectationJ G β J {y, g} * gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅ (fun m => notConnComp G m o = S) ≥ gatedSourcePairSum G β J {o, x} ∅ (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) := by
-- proof
  apply StatMech.Sharpness.claim1_ising_unconditional_cleared G β J hβ hJ S o x y g ho hx hy hg hyg

/--
[claim1_ising_self_cleared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma claim1_ising_self_cleared_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {o y g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (ho : o ∉ S)
  (hy : y ∈ S)
  (hg : g ∈ S)
  (hyg : y ≠ g) :
-- imply
  expectationJ G β J {y, g} * gatedSourcePairSum G β J {y, g} ∅ (fun m => notConnComp G m o = S) ≥ gatedSourcePairSum G β J ∅ ∅ (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) := by
-- proof
  apply StatMech.Sharpness.claim1_ising_self_cleared G β J hβ hJ S o y g ho hy hg hyg

/--
[claim1_ising_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean)
-/
@[path]
private lemma claim1_ising_unconditional_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {o x y g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (ho : o ∉ S)
  (hx : x ∉ S)
  (hy : y ∈ S)
  (hg : g ∈ S)
  (hyg : y ≠ g)
  (hm : 0 < expectationJ G β J {y, g}) :
-- imply
  gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅ (fun m => notConnComp G m o = S) ≥ (expectationJ G β J {y, g})⁻¹ * gatedSourcePairSum G β J {o, x} ∅ (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) := by
-- proof
  apply StatMech.Sharpness.claim1_ising_unconditional G β J hβ hJ S o x y g ho hx hy hg hyg hm


-- created on 2026-10-23
