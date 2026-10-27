import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLieb.Part2
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[walk_firstExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLieb.lean)
-/
@[path]
private lemma walk_firstExit_eq
  {G : SimpleGraph V}
  {o z : V}
  {w : G.Walk o z}
  {S : Finset V}
  [DecidablePred (fun i => w.getVert i ∉ S)]
-- given
  (ho : o ∈ S)
  (hz : z ∉ S) :
-- imply
  ∃ k, 1 ≤ k ∧ k ≤ w.length ∧ w.getVert k ∉ S ∧ w.getVert (k - 1) ∈ S ∧ G.Adj (w.getVert (k - 1)) (w.getVert k) ∧ (∀ j < k, w.getVert j ∈ S) := by
-- proof
  apply StatMech.Sharpness.walk_firstExit w S ho hz

/--
[backbone_getVert_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLieb.lean)
-/
@[path]
private lemma backbone_getVert_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {a b : V}
  {p : IsBackbonePath G n a b}
  {i : ℕ}
-- given
  (hi : i < p.1.length) :
-- imply
  G.Adj (p.1.getVert i) (p.1.getVert (i + 1)) ∧ Odd (n s(p.1.getVert i, p.1.getVert (i + 1))) := by
-- proof
  apply StatMech.Sharpness.backbone_getVert_odd G p hi

/--
[backbone_firstExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLieb.lean)
-/
@[path]
private lemma backbone_firstExit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {o z : V}
  {p : IsBackbonePath G n o z}
  {S : Finset V}
-- given
  (ho : o ∈ S)
  (hz : z ∉ S) :
-- imply
  ∃ k : ℕ, 1 ≤ k ∧ k ≤ p.1.length ∧ p.1.getVert (k - 1) ∈ S ∧ p.1.getVert k ∉ S ∧ s(p.1.getVert (k - 1), p.1.getVert k) ∈ G.edgeFinset ∧ Odd (n s(p.1.getVert (k - 1), p.1.getVert k)) ∧ 1 ≤ n s(p.1.getVert (k - 1), p.1.getVert k) ∧ (∀ j < k, p.1.getVert j ∈ S) := by
-- proof
  apply StatMech.Sharpness.backbone_firstExit G p S ho hz

/--
[backbone_firstExit_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLieb.lean)
-/
@[path]
private lemma backbone_firstExit_crossing_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {o z : V}
  {p : IsBackbonePath G n o z}
  {S : Finset V}
-- given
  (ho : o ∈ S)
  (hz : z ∉ S) :
-- imply
  ∃ x y : V, x ∈ S ∧ y ∉ S ∧ s(x, y) ∈ G.edgeFinset ∧ 1 ≤ n s(x, y) := by
-- proof
  apply StatMech.Sharpness.backbone_firstExit_crossing G p S ho hz

/--
[tanh_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLieb.lean)
-/
@[path]
private lemma tanh_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t : ℝ}
-- given
  (ht : 0 ≤ t) :
-- imply
  0 ≤ Real.tanh t := by
-- proof
  apply StatMech.Sharpness.tanh_nonneg G ht

/--
[simonWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLieb.lean)
-/
@[path]
private lemma simonWeight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {o : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hcorr : ∀ x, 0 ≤ expectationJ G β (couplingIn J S) {o, x}) :
-- imply
  ∀ x y, 0 ≤ simonWeight G β J S o x y := by
-- proof
  apply StatMech.Sharpness.simonWeight_nonneg G β J S o hβ hJ hcorr

/--
[localized_correlation_of_claim2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLieb.lean)
-/
@[path]
private lemma localized_correlation_of_claim2_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {g : V}
  {o x : V}
-- given
  (hg : g ∉ S)
  (h0 : o ∈ S)
  (hx : x ∈ S)
  (hZ : currentSum G β (couplingIn J S) ∅ ≠ 0)
  (hden : (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0) * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S then 1 else 0)) ≠ 0) :
-- imply
  expectationJ G β (couplingIn J S) {o, x} = (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if sources G (ofEdgeFun G pq.1) = {o, x} then weight G β J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0) * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S then 1 else 0)) / (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0) * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S then 1 else 0)) := by
-- proof
  apply StatMech.Sharpness.localized_correlation_of_claim2 G β J S g hg o x h0 hx hZ hden

/--
[simonLieb_of_firstExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLieb.lean)
-/
@[path]
private lemma simonLieb_of_firstExit_eq
  {τ : V → V → ℝ}
  {o : V}
  {S : Finset V}
  {simWeight : V → V → ℝ}
  {boundaryTargets : Finset V}
-- given
  (hτ : ∀ a b, 0 ≤ τ a b)
  (hw : ∀ x y, 0 ≤ simWeight x y)
  (hbound : ∀ z, z ∉ S → τ o z ≤ ∑ x ∈ S, ∑ y ∈ boundaryTargets, simWeight x y * τ y z) :
-- imply
  SimonLieb τ o S simWeight boundaryTargets where τ_nonneg := by
-- proof
  apply StatMech.Sharpness.simonLieb_of_firstExit τ o S simWeight boundaryTargets hτ hw hbound

/--
[simonLieb_simonWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLieb.lean)
-/
@[path]
private lemma simonLieb_simonWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {o : V}
  {boundaryTargets : Finset V}
  {τ : V → V → ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hcorr : ∀ x, 0 ≤ expectationJ G β (couplingIn J S) {o, x})
  (hτ : ∀ a b, 0 ≤ τ a b)
  (hbound : ∀ z, z ∉ S → τ o z ≤ ∑ x ∈ S, ∑ y ∈ boundaryTargets, simonWeight G β J S o x y * τ y z) :
-- imply
  SimonLieb τ o S (simonWeight G β J S o) boundaryTargets := by
-- proof
  apply StatMech.Sharpness.simonLieb_simonWeight G β J S o boundaryTargets τ hβ hJ hcorr hτ hbound

/--
[simonConst_simonWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLieb.lean)
-/
@[path]
private lemma simonConst_simonWeight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {o : V}
  {boundaryTargets : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hcorr : ∀ x, 0 ≤ expectationJ G β (couplingIn J S) {o, x}) :
-- imply
  0 ≤ simonConst S (simonWeight G β J S o) boundaryTargets := by
-- proof
  apply StatMech.Sharpness.simonConst_simonWeight_nonneg G β J S o boundaryTargets hβ hJ hcorr


-- created on 2026-10-23
