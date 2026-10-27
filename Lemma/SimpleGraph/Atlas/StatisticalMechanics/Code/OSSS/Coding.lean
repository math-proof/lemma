import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.Coding


/--
[condProbBit_true_add_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma condProbBit_true_add_false_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {η : ConfigSpace E}
  {e : E}
-- given
  (hF : condNorm μ F η ≠ 0) :
-- imply
  condProbBit μ F η e true + condProbBit μ F η e false = 1 := by
-- proof
  apply StatMech.OSSS.Coding.condProbBit_true_add_false μ F η e hF

/--
[condProbBit_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma condProbBit_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {η : ConfigSpace E}
  {e : E}
  {b : Bool}
-- given
  (hμ : ∀ ω, 0 ≤ μ ω)
  (hF : 0 < condNorm μ F η) :
-- imply
  0 ≤ condProbBit μ F η e b := by
-- proof
  apply StatMech.OSSS.Coding.condProbBit_nonneg hμ F η e b hF

/--
[condProbBit_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma condProbBit_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {η : ConfigSpace E}
  {e : E}
  {b : Bool}
-- given
  (hμ : ∀ ω, 0 ≤ μ ω)
  (hF : 0 < condNorm μ F η) :
-- imply
  condProbBit μ F η e b ≤ 1 := by
-- proof
  apply StatMech.OSSS.Coding.condProbBit_le_one hμ F η e b hF

/--
[agree_congr_of_eq_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma agree_congr_of_eq_on_eq
  [Fintype E]
  [DecidableEq E]
  {F : Finset E}
  {η η' ω : ConfigSpace E}
-- given
  (h : ∀ f ∈ F, η f = η' f) :
-- imply
  Agree F η ω ↔ Agree F η' ω := by
-- proof
  apply StatMech.OSSS.Coding.agree_congr_of_eq_on F η η' ω h

/--
[condNorm_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma condNorm_congr_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {η η' : ConfigSpace E}
-- given
  (h : ∀ f ∈ F, η f = η' f) :
-- imply
  condNorm μ F η = condNorm μ F η' := by
-- proof
  apply StatMech.OSSS.Coding.condNorm_congr μ F η η' h

/--
[condProbBit_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma condProbBit_congr_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {η η' : ConfigSpace E}
  {e : E}
  {b : Bool}
-- given
  (h : ∀ f ∈ F, η f = η' f) :
-- imply
  condProbBit μ F η e b = condProbBit μ F η' e b := by
-- proof
  apply StatMech.OSSS.Coding.condProbBit_congr μ F η η' e b h

/--
[condProbClosed_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma condProbClosed_congr_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {η η' : ConfigSpace E}
  {e : E}
-- given
  (h : ∀ f ∈ F, η f = η' f) :
-- imply
  condProbClosed μ F η e = condProbClosed μ F η' e := by
-- proof
  apply StatMech.OSSS.Coding.condProbClosed_congr μ F η η' e h

/--
[prefixIdx_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma prefixIdx_zero_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ} :
-- imply
  prefixIdx n 0 = ∅ := by
-- proof
  apply StatMech.OSSS.Coding.prefixIdx_zero n

/--
[prefixIdx_succ_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma prefixIdx_succ_lt_eq
  [Fintype E]
  [DecidableEq E]
  {n t : ℕ}
-- given
  (ht : t < n) :
-- imply
  prefixIdx n (t+1) = insert (⟨t, ht⟩ : Fin n) (prefixIdx n t) := by
-- proof
  apply StatMech.OSSS.Coding.prefixIdx_succ_lt n t ht

/--
[prefixIdx_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma prefixIdx_ge_eq
  [Fintype E]
  [DecidableEq E]
  {n t : ℕ}
-- given
  (ht : n ≤ t) :
-- imply
  prefixIdx n t = Finset.univ := by
-- proof
  apply StatMech.OSSS.Coding.prefixIdx_ge n t ht

/--
[prefixIdx_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma prefixIdx_self_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ} :
-- imply
  prefixIdx n n = Finset.univ := by
-- proof
  apply StatMech.OSSS.Coding.prefixIdx_self n

/--
[prefixIdx_succ_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma prefixIdx_succ_ge_eq
  [Fintype E]
  [DecidableEq E]
  {n t : ℕ}
-- given
  (ht : n ≤ t) :
-- imply
  prefixIdx n (t+1) = prefixIdx n t := by
-- proof
  apply StatMech.OSSS.Coding.prefixIdx_succ_ge n t ht

/--
[mem_prefixIdx_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma mem_prefixIdx_lt_eq
  [Fintype E]
  [DecidableEq E]
  {n t : ℕ}
-- given
  (ht : t < n) :
-- imply
  (⟨t, ht⟩ : Fin n) ∉ prefixIdx n t := by
-- proof
  apply StatMech.OSSS.Coding.mem_prefixIdx_lt n t ht

/--
[mem_prefixSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma mem_prefixSet_iff_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n → E}
  {k : ℕ}
  {e : E} :
-- imply
  e ∈ prefixSet σ k ↔ ∃ s : Fin n, (s : ℕ) < k ∧ σ s = e := by
-- proof
  apply StatMech.OSSS.Coding.mem_prefixSet_iff σ k e

/--
[prefixSet_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma prefixSet_zero_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n → E} :
-- imply
  prefixSet σ 0 = ∅ := by
-- proof
  apply StatMech.OSSS.Coding.prefixSet_zero σ

/--
[prefixSet_succ_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma prefixSet_succ_lt_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n → E}
  {t : ℕ}
-- given
  (ht : t < n) :
-- imply
  prefixSet σ (t+1) = insert (σ ⟨t, ht⟩) (prefixSet σ t) := by
-- proof
  apply StatMech.OSSS.Coding.prefixSet_succ_lt σ t ht

/--
[prefixSet_succ_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma prefixSet_succ_ge_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n → E}
  {t : ℕ}
-- given
  (ht : n ≤ t) :
-- imply
  prefixSet σ (t+1) = prefixSet σ t := by
-- proof
  apply StatMech.OSSS.Coding.prefixSet_succ_ge σ t ht

/--
[prefixSet_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma prefixSet_card_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n ≃ E} :
-- imply
  prefixSet (σ : Fin n → E) n = Finset.univ := by
-- proof
  apply StatMech.OSSS.Coding.prefixSet_card σ

/--
[condNorm_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma condNorm_insert_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {η : ConfigSpace E}
  {e : E} :
-- imply
  condNorm μ (insert e F) η = ∑ ω, if (Agree F η ω ∧ ω e = η e) then μ ω else 0 := by
-- proof
  apply StatMech.OSSS.Coding.condNorm_insert μ F η e

/--
[condProbBit_eq_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma condProbBit_eq_ratio_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {η : ConfigSpace E}
  {e : E} :
-- imply
  condProbBit μ F η e (η e) = condNorm μ (insert e F) η / condNorm μ F η := by
-- proof
  apply StatMech.OSSS.Coding.condProbBit_eq_ratio μ F η e

/--
[telescope_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma telescope_step_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {η : ConfigSpace E}
  {e : E}
-- given
  (hF : condNorm μ F η ≠ 0) :
-- imply
  condNorm μ (insert e F) η = condProbBit μ F η e (η e) * condNorm μ F η := by
-- proof
  apply StatMech.OSSS.Coding.telescope_step μ F η e hF

/--
[condNorm_prefix_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma condNorm_prefix_telescope_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {η : ConfigSpace E}
  {t : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  condNorm μ (prefixSet σ t) η = (∏ s ∈ prefixIdx n t, condProbBit μ (prefixSet σ (s : ℕ)) η (σ s) (η (σ s))) * condNorm μ (∅ : Finset E) η := by
-- proof
  apply StatMech.OSSS.Coding.condNorm_prefix_telescope μ hpos σ η t

/--
[condNorm_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma condNorm_empty_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {η : ConfigSpace E} :
-- imply
  condNorm μ (∅ : Finset E) η = ∑ ω, μ ω := by
-- proof
  apply StatMech.OSSS.Coding.condNorm_empty μ η

/--
[condNorm_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma condNorm_univ_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {η : ConfigSpace E} :
-- imply
  condNorm μ (Finset.univ : Finset E) η = μ η := by
-- proof
  apply StatMech.OSSS.Coding.condNorm_univ μ η

/--
[codePrefix_succ_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma codePrefix_succ_self_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {u : Fin n → ℝ}
  {t : ℕ}
-- given
  (ht : t < n) :
-- imply
  codePrefix μ σ u (t+1) (σ ⟨t, ht⟩) = decide (u ⟨t, ht⟩ ≥ condProbClosed μ (prefixSet σ t) (codePrefix μ σ u t) (σ ⟨t, ht⟩)) := by
-- proof
  apply StatMech.OSSS.Coding.codePrefix_succ_self μ σ u t ht

/--
[codePrefix_stable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma codePrefix_stable_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {u : Fin n → ℝ}
  {k m : ℕ}
  {e : E}
-- given
  (hσ : Function.Injective σ)
  (hkm : k ≤ m)
  (he : e ∈ prefixSet σ k) :
-- imply
  codePrefix μ σ u m e = codePrefix μ σ u k e := by
-- proof
  apply StatMech.OSSS.Coding.codePrefix_stable μ σ hσ u k m hkm e he

/--
[codePrefix_agree_codeMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma codePrefix_agree_codeMap_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {u : Fin n → ℝ}
  {m : ℕ}
-- given
  (hσ : Function.Injective σ)
  (hm : m ≤ n) :
-- imply
  ∀ e ∈ prefixSet σ m, codePrefix μ σ u m e = codeMap μ σ u e := by
-- proof
  apply StatMech.OSSS.Coding.codePrefix_agree_codeMap μ σ hσ u m hm

/--
[recon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma recon_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {x : ConfigSpace E}
  {u : Fin n → ℝ}
  {m : ℕ}
-- given
  (hσ : Function.Injective σ)
  (hm : m ≤ n)
  (H : ∀ (t : ℕ) (ht : t < m), x (σ ⟨t, by omega⟩) = decide (u ⟨t, by omega⟩ ≥ thr μ σ x ⟨t, by omega⟩)) :
-- imply
  Agree (prefixSet σ m) x (codePrefix μ σ u m) := by
-- proof
  apply StatMech.OSSS.Coding.recon μ σ hσ x u m hm H

/--
[codeMap_eq_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma codeMap_eq_imp_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {x : ConfigSpace E}
  {u : Fin n → ℝ}
  {t : Fin n}
-- given
  (hσ : Function.Injective σ)
  (hx : codeMap μ σ u = x) :
-- imply
  x (σ t) = decide (u t ≥ thr μ σ x t) := by
-- proof
  apply StatMech.OSSS.Coding.codeMap_eq_imp μ σ hσ x u hx t

/--
[codeMap_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma codeMap_eq_iff_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E}
  {u : Fin n → ℝ} :
-- imply
  codeMap μ (σ : Fin n → E) u = x ↔ ∀ t : Fin n, x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t) := by
-- proof
  apply StatMech.OSSS.Coding.codeMap_eq_iff μ σ x u

/--
[thr_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma thr_mem_Icc_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {x : ConfigSpace E}
  {t : Fin n}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  0 ≤ thr μ σ x t ∧ thr μ σ x t ≤ 1 := by
-- proof
  apply StatMech.OSSS.Coding.thr_mem_Icc μ hpos σ x t

/--
[codeFibre_eq_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma codeFibre_eq_box_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  codeFibre μ σ x = Set.univ.pi (codeInterval μ (σ : Fin n → E) x) := by
-- proof
  apply StatMech.OSSS.Coding.codeFibre_eq_box μ hpos σ x

/--
[volume_codeInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma volume_codeInterval_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {x : ConfigSpace E}
  {t : Fin n}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  (volume (codeInterval μ σ x t)).toReal = condProbBit μ (prefixSet σ (t : ℕ)) x (σ t) (x (σ t)) := by
-- proof
  apply StatMech.OSSS.Coding.volume_codeInterval μ hpos σ x t

/--
[codeProb_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma codeProb_eq_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (∏ t : Fin n, condProbBit μ (prefixSet (σ : Fin n → E) (t : ℕ)) x ((σ : Fin n → E) t) (x ((σ : Fin n → E) t))) = μ x := by
-- proof
  apply StatMech.OSSS.Coding.codeProb_eq_mass μ hpos hμ1 σ x

/--
[volume_codeFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma volume_codeFibre_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (volume (codeFibre μ σ x)).toReal = μ x := by
-- proof
  apply StatMech.OSSS.Coding.volume_codeFibre μ hpos hμ1 σ x

/--
[eval_eq_of_agree_on_queried](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma eval_eq_of_agree_on_queried_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω ω' : ConfigSpace E}
-- given
  (h : ∀ e ∈ T.queried ω, ω' e = ω e) :
-- imply
  T.eval ω' = T.eval ω := by
-- proof
  apply StatMech.OSSS.Coding.eval_eq_of_agree_on_queried T ω ω' h

/--
[stoppingTime_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma stoppingTime_eq_card_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E} :
-- imply
  stoppingTime T ω = (T.queried ω).card := by
-- proof
  apply StatMech.OSSS.Coding.stoppingTime_eq_card T ω

/--
[eval_determined_by_queried](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean)
-/
@[path]
private lemma eval_determined_by_queried_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω ω' : ConfigSpace E}
-- given
  (h : ∀ e ∈ T.queried ω, ω' e = ω e) :
-- imply
  T.eval ω' = T.eval ω := by
-- proof
  apply StatMech.OSSS.Coding.eval_determined_by_queried T ω ω' h


-- created on 2026-10-23
