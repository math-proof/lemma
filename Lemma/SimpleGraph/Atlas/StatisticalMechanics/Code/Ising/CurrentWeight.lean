import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.CurrentWeight
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Ising


/--
[acw_weight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean)
-/
@[path]
private lemma acw_weight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n : Current V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ weight G β J n := by
-- proof
  apply StatMech.Ising.acw_weight_nonneg G β J hβ hJ n

/--
[acw_weight_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean)
-/
@[path]
private lemma acw_weight_restrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  [DecidablePred p]
  {n : Current V}
-- given
  (p : Sym2 V → Prop) :
-- imply
  weight G β J (acwRestrict p n) = ∏ e ∈ G.edgeFinset.filter p, (β * J e) ^ (n e) / (Nat.factorial (n e)) := by
-- proof
  apply StatMech.Ising.acw_weight_restrict G β J p n

/--
[acw_weight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean)
-/
@[path]
private lemma acw_weight_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  [DecidablePred p]
  {n : Current V}
-- given
  (p : Sym2 V → Prop) :
-- imply
  weight G β J n = weight G β J (acwRestrict p n) * weight G β J (acwRestrict (fun e => ¬ p e) n) := by
-- proof
  apply StatMech.Ising.acw_weight_factor G β J p n

/--
[acw_weight_factor_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean)
-/
@[path]
private lemma acw_weight_factor_cut_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {n : Current V} :
-- imply
  weight G β J n = weight G β J (acwRestrict (acwInternal S) n) * weight G β J (acwRestrict (fun e => ¬ acwInternal S e) n) := by
-- proof
  apply StatMech.Ising.acw_weight_factor_cut G β J S n

/--
[acw_incidentFlux_internal_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean)
-/
@[path]
private lemma acw_incidentFlux_internal_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Current V}
  {x : V}
-- given
  (hcut : acwClosedCut G S)
  (hx : x ∈ S) :
-- imply
  Sharpness.incidentFlux G (acwRestrict (acwInternal S) n) x = Sharpness.incidentFlux G n x := by
-- proof
  apply StatMech.Ising.acw_incidentFlux_internal_mem G S hcut n hx

/--
[acw_incidentFlux_internal_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean)
-/
@[path]
private lemma acw_incidentFlux_internal_not_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Current V}
  {x : V}
-- given
  (hx : x ∉ S) :
-- imply
  Sharpness.incidentFlux G (acwRestrict (acwInternal S) n) x = 0 := by
-- proof
  apply StatMech.Ising.acw_incidentFlux_internal_not_mem G S n hx

/--
[acw_sources_internal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean)
-/
@[path]
private lemma acw_sources_internal_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  Sharpness.sources G (acwRestrict (acwInternal S) n) = (Sharpness.sources G n) ∩ S := by
-- proof
  apply StatMech.Ising.acw_sources_internal_eq G S hcut n

/--
[acw_sources_external_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean)
-/
@[path]
private lemma acw_sources_external_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n) = (Sharpness.sources G n) ∩ Sᶜ := by
-- proof
  apply StatMech.Ising.acw_sources_external_eq G S hcut n

/--
[acw_sources_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean)
-/
@[path]
private lemma acw_sources_partition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  Sharpness.sources G n = Sharpness.sources G (acwRestrict (acwInternal S) n) ∪ Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n) ∧ Disjoint (Sharpness.sources G (acwRestrict (acwInternal S) n)) (Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n)) := by
-- proof
  apply StatMech.Ising.acw_sources_partition G S hcut n

/--
[acw_currentSum_eq_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean)
-/
@[path]
private lemma acw_currentSum_eq_expectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (h0 : Sharpness.currentSum G β J ∅ ≠ 0) :
-- imply
  Sharpness.currentSum G β J A = Sharpness.expectationJ G β J A * Sharpness.currentSum G β J ∅ := by
-- proof
  apply StatMech.Ising.acw_currentSum_eq_expectation G β J A h0

/--
[acw_currentSum_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean)
-/
@[path]
private lemma acw_currentSum_ratio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
-- given
  (h0 : Sharpness.currentSum G β J ∅ ≠ 0)
  (hA : Sharpness.expectationJ G β J A ≠ 0) :
-- imply
  Sharpness.currentSum G β J B = (Sharpness.expectationJ G β J B / Sharpness.expectationJ G β J A) * Sharpness.currentSum G β J A := by
-- proof
  apply StatMech.Ising.acw_currentSum_ratio G β J A B h0 hA

/--
[acw_crossClass_closure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean)
-/
@[path]
private lemma acw_crossClass_closure_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset (Finset ι)}
  {A : Finset V}
  {o x y : V}
  {Φ : Finset ι → Finset ι → ℝ}
-- given
  (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : ∀ m ∈ M, Sharpness.RandomCurrent.sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
  (hratio : 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A) ≤ ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) :
-- imply
  0 ≤ ∑ m ∈ M, aie_gap ends m (Φ m) A o x y := by
-- proof
  apply StatMech.Ising.acw_crossClass_closure G ends M hnd A hm hox hoy hxy Φ hΦ hratio

/--
[acw_ratioFreeDom_holds_of_no_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean)
-/
@[path]
private lemma acw_ratioFreeDom_holds_of_no_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset (Finset ι)}
  {A : Finset V}
  {o x y : V}
  {Φ : Finset ι → Finset ι → ℝ}
-- given
  (hΦnn : ∀ m K, 0 ≤ (Φ m) K)
  (hno : M.filter (fun m => aie_allConn ends m o x y) = ∅) :
-- imply
  acw_ratioFreeDom ends M A o x y Φ := by
-- proof
  apply StatMech.Ising.acw_ratioFreeDom_holds_of_no_allConn G ends M A Φ hΦnn hno

/--
[acw_ratioFreeDom_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean)
-/
@[path]
private lemma acw_ratioFreeDom_refutable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ¬ acw_ratioFreeDom (V := Fin 3) ahd_triEnds ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) (Sharpness.RandomCurrent.sources ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) 0 1 2 (fun _ _ => 1) := by
-- proof
  apply StatMech.Ising.acw_ratioFreeDom_refutable G


-- created on 2026-10-23
