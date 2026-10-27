import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpnessFull.Part2
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[localized_two_point_of_claim2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessFull.lean)
-/
@[path]
private lemma localized_two_point_of_claim2_eq
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
  (hZ : currentSum G β (couplingIn J S) ∅ ≠ 0)
  (hden : (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0) * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S then 1 else 0)) ≠ 0) :
-- imply
  expectationJ G β (couplingIn J S) {zero, x} = (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if sources G (ofEdgeFun G pq.1) = {zero, x} then weight G β J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0) * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S then 1 else 0)) / (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0) * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S then 1 else 0)) := by
-- proof
  apply StatMech.Sharpness.localized_two_point_of_claim2 G β J S g hg zero x h0 hx hZ hden

/--
[simonConst_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessFull.lean)
-/
@[path]
private lemma simonConst_nonneg_eq
  {S : Finset V}
  {simWeight : V → V → ℝ}
  {boundaryTargets : Finset V}
-- given
  (hw : ∀ x y, 0 ≤ simWeight x y) :
-- imply
  0 ≤ simonConst S simWeight boundaryTargets := by
-- proof
  apply StatMech.Sharpness.simonConst_nonneg S simWeight boundaryTargets hw

/--
[susceptibility_self_consistent_sl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessFull.lean)
-/
@[path]
private lemma susceptibility_self_consistent_sl_eq
  [DecidableEq V]
  {τ : V → V → ℝ}
  {o : V}
  {S : Finset V}
  {simWeight : V → V → ℝ}
  {boundaryTargets : Finset V}
  {Λ : Finset V}
  {χbar : ℝ}
-- given
  (hSL : SimonLieb τ o S simWeight boundaryTargets)
  (hχbar : ∀ y ∈ boundaryTargets, ∑ z ∈ Λ \ S, τ y z ≤ χbar)
  (hχnn : 0 ≤ χbar)
  (hSbound : ∑ z ∈ Λ ∩ S, τ o z ≤ (S.card : ℝ)) :
-- imply
  ∑ z ∈ Λ, τ o z ≤ (S.card : ℝ) + simonConst S simWeight boundaryTargets * χbar := by
-- proof
  apply StatMech.Sharpness.susceptibility_self_consistent_sl τ o S simWeight boundaryTargets hSL Λ χbar hχbar hχnn hSbound

/--
[susceptibility_solve](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessFull.lean)
-/
@[path]
private lemma susceptibility_solve_eq
  {χ Sval φ : ℝ}
-- given
  (hχ : 0 ≤ χ)
  (hφ1 : φ < 1)
  (hself : χ ≤ Sval + φ * χ) :
-- imply
  χ ≤ Sval / (1 - φ) := by
-- proof
  apply StatMech.Sharpness.susceptibility_solve χ Sval φ hχ hφ1 hself

/--
[susceptibility_uniform_of_simon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessFull.lean)
-/
@[path]
private lemma susceptibility_uniform_of_simon_eq
  {S : Finset V}
  {simWeight : V → V → ℝ}
  {boundaryTargets : Finset V}
  {χbar : ℝ}
-- given
  (hχnn : 0 ≤ χbar)
  (hφ1 : simonConst S simWeight boundaryTargets < 1)
  (hself : χbar ≤ (S.card : ℝ) + simonConst S simWeight boundaryTargets * χbar) :
-- imply
  χbar ≤ (S.card : ℝ) / (1 - simonConst S simWeight boundaryTargets) := by
-- proof
  apply StatMech.Sharpness.susceptibility_uniform_of_simon S simWeight boundaryTargets χbar hχnn hφ1 hself

/--
[decay_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessFull.lean)
-/
@[path]
private lemma decay_iterate_eq
  {φ : ℝ}
  {f : ℕ → ℝ}
-- given
  (hφ0 : 0 ≤ φ)
  (hf0 : f 0 ≤ 1)
  (hstep : ∀ k, f (k + 1) ≤ φ * f k) :
-- imply
  ∀ k, f k ≤ φ ^ k := by
-- proof
  apply StatMech.Sharpness.decay_iterate φ hφ0 f hf0 hstep

/--
[exponential_decay_of_geom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessFull.lean)
-/
@[path]
private lemma exponential_decay_of_geom_eq
  {φ : ℝ}
  {L : ℕ}
-- given
  (hφ0 : 0 < φ)
  (hφ1 : φ < 1)
  (hL : 1 ≤ L) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ n : ℕ, φ ^ (n / L) ≤ C * Real.exp (-c * n) := by
-- proof
  apply StatMech.Sharpness.exponential_decay_of_geom φ hφ0 hφ1 L hL

/--
[exponential_decay_of_simon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessFull.lean)
-/
@[path]
private lemma exponential_decay_of_simon_eq
  {φ : ℝ}
  {L : ℕ}
  {f : ℕ → ℝ}
-- given
  (hφ0 : 0 < φ)
  (hφ1 : φ < 1)
  (hL : 1 ≤ L)
  (hfnn : ∀ n, 0 ≤ f n)
  (hf0 : f 0 ≤ 1)
  (hstep : ∀ k, f ((k + 1) * L) ≤ φ * f (k * L))
  (hmono : ∀ m n, m ≤ n → f n ≤ f m) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ n : ℕ, f n ≤ C * Real.exp (-c * n) := by
-- proof
  apply StatMech.Sharpness.exponential_decay_of_simon φ hφ0 hφ1 L hL f hfnn hf0 hstep hmono

/--
[ising_sharpness_finite_susceptibility](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessFull.lean)
-/
@[path]
private lemma ising_sharpness_finite_susceptibility_eq
  [DecidableEq V]
  {τ : V → V → ℝ}
  {o : V}
  {S : Finset V}
  {simWeight : V → V → ℝ}
  {boundaryTargets : Finset V}
  {Λ W : Finset V}
-- given
  (hSL : SimonLieb τ o S simWeight boundaryTargets)
  (hφ1 : simonConst S simWeight boundaryTargets < 1)
  (hχbarW : ∀ y ∈ boundaryTargets, ∑ z ∈ W \ S, τ y z ≤ ∑ z ∈ W, τ o z)
  (hSboundW : ∑ z ∈ W ∩ S, τ o z ≤ (S.card : ℝ))
  (hΛbar : ∑ z ∈ Λ, τ o z ≤ ∑ z ∈ W, τ o z) :
-- imply
  ∑ z ∈ Λ, τ o z ≤ (S.card : ℝ) / (1 - simonConst S simWeight boundaryTargets) := by
-- proof
  apply StatMech.Sharpness.ising_sharpness_finite_susceptibility τ o S simWeight boundaryTargets hSL hφ1 Λ W hχbarW hSboundW hΛbar


-- created on 2026-10-23
