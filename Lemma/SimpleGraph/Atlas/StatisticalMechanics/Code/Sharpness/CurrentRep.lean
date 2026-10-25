import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
open Finset SimpleGraph StatMech StatMech.Sharpness


/--
[prod_tsum_fubini](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma prod_tsum_fubini_eq
  [DecidableEq ι]
  {g : ι → ℕ → ℝ}
  {s : Finset ι}
-- given
  (hg : ∀ i, Summable (g i))
  (hgnn : ∀ i k, 0 ≤ g i k) :
-- imply
  Summable (fun m : ↥s → ℕ => ∏ i : ↥s, g i.1 (m i)) ∧ (∏ i ∈ s, ∑' k : ℕ, g i k) = ∑' (m : ↥s → ℕ), ∏ i : ↥s, g i.1 (m i) := by
-- proof
  apply StatMech.Sharpness.prod_tsum_fubini g hg hgnn s

/--
[summable_prod_signed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma summable_prod_signed_eq
  [DecidableEq ι]
  {g : ι → ℕ → ℝ}
  {s : Finset ι}
-- given
  (hgn : ∀ i, Summable (fun k => ‖g i k‖)) :
-- imply
  Summable (fun m : ↥s → ℕ => ∏ i : ↥s, g i.1 (m i)) := by
-- proof
  apply StatMech.Sharpness.summable_prod_signed g hgn s

/--
[signed_prod_tsum_fubini](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma signed_prod_tsum_fubini_eq
  [DecidableEq ι]
  {g : ι → ℕ → ℝ}
  {s : Finset ι}
-- given
  (hg : ∀ i, Summable (g i))
  (hgn : ∀ i, Summable (fun k => ‖g i k‖)) :
-- imply
  (∏ i ∈ s, ∑' k : ℕ, g i k) = ∑' (m : ↥s → ℕ), ∏ i : ↥s, g i.1 (m i) := by
-- proof
  apply StatMech.Sharpness.signed_prod_tsum_fubini g hg hgn s

/--
[sum_spinB_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma sum_spinB_pow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ℕ} :
-- imply
  (∑ b : Bool, (spinB b) ^ m) = if Even m then 2 else 0 := by
-- proof
  apply StatMech.Sharpness.sum_spinB_pow G m

/--
[bond_pow_eq_prod_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma bond_pow_eq_prod_filter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
  {e : Sym2 V}
  {k : ℕ}
-- given
  (he : e ∈ G.edgeFinset) :
-- imply
  (bond s e) ^ k = ∏ v ∈ univ.filter (fun v => v ∈ e), (spin s v) ^ k := by
-- proof
  apply StatMech.Sharpness.bond_pow_eq_prod_filter G s e he k

/--
[prod_bond_pow_eq_prod_spin_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma prod_bond_pow_eq_prod_spin_pow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {s : ConfigSpace V} :
-- imply
  (∏ e ∈ G.edgeFinset, (bond s e) ^ (n e)) = ∏ v : V, (spin s v) ^ (incidentFlux G n v) := by
-- proof
  apply StatMech.Sharpness.prod_bond_pow_eq_prod_spin_pow G n s

/--
[sum_prod_spin_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma sum_prod_spin_pow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : V → ℕ} :
-- imply
  (∑ s : ConfigSpace V, ∏ v : V, (spin s v) ^ (e v)) = ∏ v : V, ∑ b : Bool, (spinB b) ^ (e v) := by
-- proof
  apply StatMech.Sharpness.sum_prod_spin_pow G e

/--
[spinProd_eq_prod_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma spinProd_eq_prod_pow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {s : ConfigSpace V} :
-- imply
  spinProd A s = ∏ v : V, (spin s v) ^ (if v ∈ A then 1 else 0) := by
-- proof
  apply StatMech.Sharpness.spinProd_eq_prod_pow G A s

/--
[spinSum_monomial_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma spinSum_monomial_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {n : Current V} :
-- imply
  (∑ s : ConfigSpace V, spinProd A s * ∏ e ∈ G.edgeFinset, (bond s e) ^ (n e)) = if sources G n = A then (2 : ℝ) ^ (Fintype.card V) else 0 := by
-- proof
  apply StatMech.Sharpness.spinSum_monomial_eq G A n

/--
[weight_ofEdgeFun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma weight_ofEdgeFun_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ} :
-- imply
  weight G β J (ofEdgeFun G m) = ∏ e : ↥G.edgeFinset, (β * J e.1) ^ (m e) / (Nat.factorial (m e)) := by
-- proof
  apply StatMech.Sharpness.weight_ofEdgeFun G β J m

/--
[prod_bond_pow_ofEdgeFun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma prod_bond_pow_ofEdgeFun_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
  {m : ↥G.edgeFinset → ℕ} :
-- imply
  (∏ e ∈ G.edgeFinset, (bond s e) ^ ((ofEdgeFun G m) e)) = ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e) := by
-- proof
  apply StatMech.Sharpness.prod_bond_pow_ofEdgeFun G s m

/--
[tsum_gEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma tsum_gEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {s : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  (∑' k, gEdge β J s e k) = Real.exp (β * J e * bond s e) := by
-- proof
  apply StatMech.Sharpness.tsum_gEdge G β J s e

/--
[summable_gEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma summable_gEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {s : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  Summable (gEdge β J s e) := by
-- proof
  apply StatMech.Sharpness.summable_gEdge G β J s e

/--
[summable_norm_gEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma summable_norm_gEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {s : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  Summable (fun k => ‖gEdge β J s e k‖) := by
-- proof
  apply StatMech.Sharpness.summable_norm_gEdge G β J s e

/--
[prod_gEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma prod_gEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {s : ConfigSpace V}
  {m : ↥G.edgeFinset → ℕ} :
-- imply
  (∏ e : ↥G.edgeFinset, gEdge β J s e.1 (m e)) = weight G β J (ofEdgeFun G m) * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e) := by
-- proof
  apply StatMech.Sharpness.prod_gEdge G β J s m

/--
[boltzmannJ_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma boltzmannJ_eq_tsum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {s : ConfigSpace V} :
-- imply
  boltzmannJ G β J s = ∑' m : ↥G.edgeFinset → ℕ, weight G β J (ofEdgeFun G m) * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e) := by
-- proof
  apply StatMech.Sharpness.boltzmannJ_eq_tsum G β J s

/--
[summable_weight_bond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma summable_weight_bond_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {s : ConfigSpace V} :
-- imply
  Summable (fun m : ↥G.edgeFinset → ℕ => weight G β J (ofEdgeFun G m) * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e)) := by
-- proof
  apply StatMech.Sharpness.summable_weight_bond G β J s

/--
[spinSum_eq_currentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma spinSum_eq_currentSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  (∑ s : ConfigSpace V, spinProd A s * boltzmannJ G β J s) = (2 : ℝ) ^ (Fintype.card V) * currentSum G β J A := by
-- proof
  apply StatMech.Sharpness.spinSum_eq_currentSum G β J A

/--
[boltzmannJ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma boltzmannJ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {s : ConfigSpace V} :
-- imply
  0 < boltzmannJ G β J s := by
-- proof
  apply StatMech.Sharpness.boltzmannJ_pos G β J s

/--
[partitionJ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma partitionJ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  0 < partitionJ G β J := by
-- proof
  apply StatMech.Sharpness.partitionJ_pos G β J

/--
[partitionJ_eq_currentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma partitionJ_eq_currentSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  partitionJ G β J = (2 : ℝ) ^ (Fintype.card V) * currentSum G β J ∅ := by
-- proof
  apply StatMech.Sharpness.partitionJ_eq_currentSum G β J

/--
[current_representation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma current_representation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  expectationJ G β J A = currentSum G β J A / currentSum G β J ∅ := by
-- proof
  apply StatMech.Sharpness.current_representation G β J A

/--
[boltzmannJ_one_eq_isingWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma boltzmannJ_one_eq_isingWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {s : ConfigSpace V} :
-- imply
  boltzmannJ G β (fun _ => 1) s = isingWeight G β 0 s := by
-- proof
  apply StatMech.Sharpness.boltzmannJ_one_eq_isingWeight G β s

/--
[partitionJ_one_eq_isingZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma partitionJ_one_eq_isingZ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ} :
-- imply
  partitionJ G β (fun _ => 1) = isingZ G β 0 := by
-- proof
  apply StatMech.Sharpness.partitionJ_one_eq_isingZ G β

/--
[expectationJ_one_eq_isingExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma expectationJ_one_eq_isingExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {A : Finset V} :
-- imply
  expectationJ G β (fun _ => 1) A = isingExpectation G β 0 (spinProd A) := by
-- proof
  apply StatMech.Sharpness.expectationJ_one_eq_isingExpectation G β A

/--
[isingExpectation_eq_currentSum_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean)
-/
@[path]
private lemma isingExpectation_eq_currentSum_ratio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {A : Finset V} :
-- imply
  isingExpectation G β 0 (spinProd A) = currentSum G β (fun _ => 1) A / currentSum G β (fun _ => 1) ∅ := by
-- proof
  apply StatMech.Sharpness.isingExpectation_eq_currentSum_ratio G β A


-- created on 2026-10-23
