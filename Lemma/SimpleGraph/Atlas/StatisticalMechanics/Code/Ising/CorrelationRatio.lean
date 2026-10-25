import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Ising


/--
[acr_currentSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CorrelationRatio.lean)
-/
@[path]
private lemma acr_currentSum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ Sharpness.currentSum G β J A := by
-- proof
  apply StatMech.Ising.acr_currentSum_nonneg G β J hβ hJ A

/--
[acr_currentSum_empty_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CorrelationRatio.lean)
-/
@[path]
private lemma acr_currentSum_empty_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  0 < Sharpness.currentSum G β J ∅ := by
-- proof
  apply StatMech.Ising.acr_currentSum_empty_pos G β J

/--
[acr_expectationJ_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CorrelationRatio.lean)
-/
@[path]
private lemma acr_expectationJ_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ Sharpness.expectationJ G β J A := by
-- proof
  apply StatMech.Ising.acr_expectationJ_nonneg G β J hβ hJ A

/--
[acr_eq15_insertion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CorrelationRatio.lean)
-/
@[path]
private lemma acr_eq15_insertion_eq
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
  apply StatMech.Ising.acr_eq15_insertion G β J A h0

/--
[acr_eq15_insertion'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CorrelationRatio.lean)
-/
@[path]
private lemma acr_eq15_insertion'_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  Sharpness.currentSum G β J A = Sharpness.expectationJ G β J A * Sharpness.currentSum G β J ∅ := by
-- proof
  apply StatMech.Ising.acr_eq15_insertion' G β J A

/--
[acr_currentSum_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CorrelationRatio.lean)
-/
@[path]
private lemma acr_currentSum_ratio_eq
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
  apply StatMech.Ising.acr_currentSum_ratio G β J A B h0 hA

/--
[acr_eq15_insertion_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CorrelationRatio.lean)
-/
@[path]
private lemma acr_eq15_insertion_sq_eq
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
  Sharpness.expectationJ G β J A * Sharpness.currentSum G β J A = (Sharpness.expectationJ G β J A) ^ 2 * Sharpness.currentSum G β J ∅ := by
-- proof
  apply StatMech.Ising.acr_eq15_insertion_sq G β J A h0

/--
[acr_claim1_griffiths_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CorrelationRatio.lean)
-/
@[path]
private lemma acr_claim1_griffiths_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {eS cS eΛ : ℝ}
-- given
  (hSnn : 0 ≤ eS)
  (hcSnn : 0 ≤ cS)
  (hgriff : eS ≤ eΛ) :
-- imply
  eΛ * (eS * cS) ≥ eS ^ 2 * cS := by
-- proof
  apply StatMech.Ising.acr_claim1_griffiths_step G eS cS eΛ hSnn hcSnn hgriff

/--
[acr_claim1_ratio_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CorrelationRatio.lean)
-/
@[path]
private lemma acr_claim1_ratio_lower_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {GS : SimpleGraph V}
  [DecidableRel GS.Adj]
  {βS : ℝ}
  {JS : Sym2 V → ℝ}
  {Asrc : Finset V}
  {eΛ : ℝ}
-- given
  (hβ : 0 ≤ βS)
  (hJ : ∀ e, 0 ≤ JS e)
  (h0 : Sharpness.currentSum GS βS JS ∅ ≠ 0)
  (hgriff : Sharpness.expectationJ GS βS JS Asrc ≤ eΛ) :
-- imply
  eΛ * Sharpness.currentSum GS βS JS Asrc ≥ (Sharpness.expectationJ GS βS JS Asrc) ^ 2 * Sharpness.currentSum GS βS JS ∅ := by
-- proof
  apply StatMech.Ising.acr_claim1_ratio_lower_bound G GS βS JS Asrc eΛ hβ hJ h0 hgriff

/--
[acr_crossClass_closure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CorrelationRatio.lean)
-/
@[path]
private lemma acr_crossClass_closure_eq
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
  apply StatMech.Ising.acr_crossClass_closure G ends M hnd A hm hox hoy hxy Φ hΦ hratio

/--
[acr_ratioDom_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CorrelationRatio.lean)
-/
@[path]
private lemma acr_ratioDom_refutable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ¬ (2 * (∑ m ∈ ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))).filter (fun m => aie_allConn ahd_triEnds m 0 1 2), aie_mass ahd_triEnds m (fun _ => 1) (StatMech.Sharpness.RandomCurrent.sources ahd_triEnds ({0, 1, 2} : Finset (Fin 3)))) ≤ ∑ m ∈ ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))).filter (fun m => aie_noneConn ahd_triEnds m 0 1 2), aie_mass ahd_triEnds m (fun _ => 1) (StatMech.Sharpness.RandomCurrent.sources ahd_triEnds ({0, 1, 2} : Finset (Fin 3)))) := by
-- proof
  apply StatMech.Ising.acr_ratioDom_refutable G


-- created on 2026-10-23
