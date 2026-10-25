import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc35bridge
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc35_hnw_mass_eq_edgeFun_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc35bridge.lean)
-/
@[path]
private lemma gc35_hnw_mass_eq_edgeFun_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m₀ : ↥G.edgeFinset → ℕ}
  {A : Finset V} :
-- imply
  hnw_mass G β J (Sharpness.ofEdgeFun G m₀) A = ∑ p : {p : ↥G.edgeFinset → ℕ // p ≤ m₀}, (if Sharpness.sources G (Sharpness.ofEdgeFun G p.1) = A then Sharpness.weight G β J (Sharpness.ofEdgeFun G p.1) * Sharpness.weight G β J (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) else 0) := by
-- proof
  apply StatMech.Walls.gc35_hnw_mass_eq_edgeFun_split G β J m₀ A

/--
[gc35_inner_second_constraint_automatic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc35bridge.lean)
-/
@[path]
private lemma gc35_inner_second_constraint_automatic_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m₀ : ↥G.edgeFinset → ℕ}
  {A B : Finset V}
-- given
  (hm : Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = A ∆ B) :
-- imply
  (∑ p : {p : ↥G.edgeFinset → ℕ // p ≤ m₀}, (if Sharpness.sources G (Sharpness.ofEdgeFun G p.1) = A then Sharpness.weight G β J (Sharpness.ofEdgeFun G p.1) * Sharpness.weight G β J (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) else 0)) = ∑ p : {p : ↥G.edgeFinset → ℕ // p ≤ m₀}, ((if Sharpness.sources G (Sharpness.ofEdgeFun G p.1) = A then Sharpness.weight G β J (Sharpness.ofEdgeFun G p.1) else 0) * (if Sharpness.sources G (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) = B then Sharpness.weight G β J (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) else 0)) := by
-- proof
  apply StatMech.Walls.gc35_inner_second_constraint_automatic G β J m₀ A B hm

/--
[gc35_inner_zero_off_fibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc35bridge.lean)
-/
@[path]
private lemma gc35_inner_zero_off_fibre_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m₀ : ↥G.edgeFinset → ℕ}
  {A B : Finset V}
-- given
  (hm : Sharpness.sources G (Sharpness.ofEdgeFun G m₀) ≠ A ∆ B) :
-- imply
  (∑ p : {p : ↥G.edgeFinset → ℕ // p ≤ m₀}, ((if Sharpness.sources G (Sharpness.ofEdgeFun G p.1) = A then Sharpness.weight G β J (Sharpness.ofEdgeFun G p.1) else 0) * (if Sharpness.sources G (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) = B then Sharpness.weight G β J (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) else 0))) = 0 := by
-- proof
  apply StatMech.Walls.gc35_inner_zero_off_fibre G β J m₀ A B hm

/--
[gc35_sourcePairSum_eq_tsum_native_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc35bridge.lean)
-/
@[path]
private lemma gc35_sourcePairSum_eq_tsum_native_mass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V} :
-- imply
  Sharpness.sourcePairSum G β J A B = ∑' m₀ : ↥G.edgeFinset → ℕ, (if Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = A ∆ B then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) A else 0) := by
-- proof
  apply StatMech.Walls.gc35_sourcePairSum_eq_tsum_native_mass G β J A B

/--
[gc35_native_mass_fibre_summand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc35bridge.lean)
-/
@[path]
private lemma gc35_native_mass_fibre_summand_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m₀ : ↥G.edgeFinset → ℕ}
  {A B : Finset V}
-- given
  (hm : Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = A ∆ B) :
-- imply
  hnw_mass G β J (Sharpness.ofEdgeFun G m₀) A = ∑ p : {p : ↥G.edgeFinset → ℕ // p ≤ m₀}, ((if Sharpness.sources G (Sharpness.ofEdgeFun G p.1) = A then Sharpness.weight G β J (Sharpness.ofEdgeFun G p.1) else 0) * (if Sharpness.sources G (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) = B then Sharpness.weight G β J (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) else 0)) := by
-- proof
  apply StatMech.Walls.gc35_native_mass_fibre_summand G β J m₀ A B hm

/--
[gc35_gated_pairSum_eq_superposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc35bridge.lean)
-/
@[path]
private lemma gc35_gated_pairSum_eq_superposition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  [DecidablePred P]
-- given
  (P : Sharpness.Current V → Prop) :
-- imply
  (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if Sharpness.sources G (Sharpness.ofEdgeFun G pq.1) = A then Sharpness.weight G β J (Sharpness.ofEdgeFun G pq.1) else 0) * (if Sharpness.sources G (Sharpness.ofEdgeFun G pq.2) = B then Sharpness.weight G β J (Sharpness.ofEdgeFun G pq.2) else 0) * (if P (fun e => Sharpness.ofEdgeFun G pq.1 e + Sharpness.ofEdgeFun G pq.2 e) then 1 else 0)) = ∑' m₀ : ↥G.edgeFinset → ℕ, (if P (Sharpness.ofEdgeFun G m₀) then 1 else 0) * ∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m₀}, ((if Sharpness.sources G (Sharpness.ofEdgeFun G K.1) = A then Sharpness.weight G β J (Sharpness.ofEdgeFun G K.1) else 0) * (if Sharpness.sources G (Sharpness.ofEdgeFun G (fun e => m₀ e - K.1 e)) = B then Sharpness.weight G β J (Sharpness.ofEdgeFun G (fun e => m₀ e - K.1 e)) else 0)) := by
-- proof
  apply StatMech.Walls.gc35_gated_pairSum_eq_superposition G β J A B P

/--
[gc35_gated_pairSum_eq_tsum_native_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc35bridge.lean)
-/
@[path]
private lemma gc35_gated_pairSum_eq_tsum_native_mass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  [DecidablePred P]
-- given
  (P : Sharpness.Current V → Prop) :
-- imply
  (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if Sharpness.sources G (Sharpness.ofEdgeFun G pq.1) = A then Sharpness.weight G β J (Sharpness.ofEdgeFun G pq.1) else 0) * (if Sharpness.sources G (Sharpness.ofEdgeFun G pq.2) = B then Sharpness.weight G β J (Sharpness.ofEdgeFun G pq.2) else 0) * (if P (fun e => Sharpness.ofEdgeFun G pq.1 e + Sharpness.ofEdgeFun G pq.2 e) then 1 else 0)) = ∑' m₀ : ↥G.edgeFinset → ℕ, (if P (Sharpness.ofEdgeFun G m₀) ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = A ∆ B then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) A else 0) := by
-- proof
  apply StatMech.Walls.gc35_gated_pairSum_eq_tsum_native_mass G β J A B P

/--
[gc35_native_resummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc35bridge.lean)
-/
@[path]
private lemma gc35_native_resummation_eq
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
  (∑' m₀ : ↥G.edgeFinset → ℕ, (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = ({zero, x} : Finset V) then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) {zero, x} else 0)) = expectationJ G β (couplingIn J S) {zero, x} * (∑' m₀ : ↥G.edgeFinset → ℕ, (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = (∅ : Finset V) then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) ∅ else 0)) := by
-- proof
  apply StatMech.Walls.gc35_native_resummation G β J S g hg zero x h0 hx hZ

/--
[gc35_native_resummation_factor_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc35bridge.lean)
-/
@[path]
private lemma gc35_native_resummation_factor_mem_Icc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {zero x : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ expectationJ G β (couplingIn J S) {zero, x} ∧ expectationJ G β (couplingIn J S) {zero, x} ≤ 1 := by
-- proof
  apply StatMech.Walls.gc35_native_resummation_factor_mem_Icc G β J hβ hJ S zero x

/--
[gc35_gc33_ma_ofEdgeFun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc35bridge.lean)
-/
@[path]
private lemma gc35_gc33_ma_ofEdgeFun_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  gc33_ma = Sharpness.ofEdgeFun gc33_G (fun i => gc33_ma i.1) := by
-- proof
  apply StatMech.Walls.gc35_gc33_ma_ofEdgeFun G

/--
[gc35_bridge_witness_mass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc35bridge.lean)
-/
@[path]
private lemma gc35_bridge_witness_mass_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  hnw_mass gc33_G 1 gc33_J gc33_ma ∅ = ∑ p : {p : ↥gc33_G.edgeFinset → ℕ // p ≤ (fun i => gc33_ma i.1)}, (if Sharpness.sources gc33_G (Sharpness.ofEdgeFun gc33_G p.1) = (∅ : Finset (Fin 5)) then Sharpness.weight gc33_G 1 gc33_J (Sharpness.ofEdgeFun gc33_G p.1) * Sharpness.weight gc33_G 1 gc33_J (Sharpness.ofEdgeFun gc33_G (fun i => (fun j => gc33_ma j.1) i - p.1 i)) else 0) := by
-- proof
  apply StatMech.Walls.gc35_bridge_witness_mass_eq G

/--
[gc35_bridge_witness_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc35bridge.lean)
-/
@[path]
private lemma gc35_bridge_witness_positive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  0 < hnw_mass gc33_G 1 gc33_J gc33_ma ∅ := by
-- proof
  apply StatMech.Walls.gc35_bridge_witness_positive G

/--
[gc35_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc35bridge.lean)
-/
@[path]
private lemma gc35_status_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {S : Finset V}
  {zero x : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  Sharpness.sourcePairSum G β J A B = ∑' m₀ : ↥G.edgeFinset → ℕ, (if Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = A ∆ B then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) A else 0) ∧ (0 ≤ expectationJ G β (couplingIn J S) {zero, x} ∧ expectationJ G β (couplingIn J S) {zero, x} ≤ 1) := by
-- proof
  apply StatMech.Walls.gc35_status G β J hβ hJ A B S zero x


-- created on 2026-10-23
