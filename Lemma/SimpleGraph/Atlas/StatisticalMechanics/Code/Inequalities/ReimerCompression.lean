import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
open MeasureTheory Finset StatMech


/--
[mem_cfgSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma mem_cfgSupport_eq
  [Fintype E]
  [DecidableEq E]
  {ω : ConfigSpace E}
  {i : E} :
-- imply
  i ∈ cfgSupport ω ↔ ω i = true := by
-- proof
  apply StatMech.mem_cfgSupport ω i

/--
[supportCfg_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma supportCfg_apply_eq
  [DecidableEq E]
  {s : Finset E}
  {i : E} :
-- imply
  supportCfg s i = decide (i ∈ s) := by
-- proof
  apply StatMech.supportCfg_apply s i

/--
[supportCfg_cfgSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma supportCfg_cfgSupport_eq
  [Fintype E]
  [DecidableEq E]
  {ω : ConfigSpace E} :
-- imply
  supportCfg (cfgSupport ω) = ω := by
-- proof
  apply StatMech.supportCfg_cfgSupport ω

/--
[cfgSupport_supportCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma cfgSupport_supportCfg_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset E} :
-- imply
  cfgSupport (supportCfg s) = s := by
-- proof
  apply StatMech.cfgSupport_supportCfg s

/--
[cfgEquivFinset_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma cfgEquivFinset_apply_eq
  [Fintype E]
  [DecidableEq E]
  {ω : ConfigSpace E} :
-- imply
  cfgEquivFinset ω = cfgSupport ω := by
-- proof
  apply StatMech.cfgEquivFinset_apply ω

/--
[cfgEquivFinset_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma cfgEquivFinset_symm_apply_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset E} :
-- imply
  cfgEquivFinset.symm s = supportCfg s := by
-- proof
  apply StatMech.cfgEquivFinset_symm_apply s

/--
[downCompress_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma downCompress_card_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)} :
-- imply
  (downCompress i 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.downCompress_card i 𝒜

/--
[mem_downCompress](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma mem_downCompress_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  ω ∈ downCompress i 𝒜 ↔ cfgSupport ω ∈ Down.compression i (𝒜.image cfgSupport) := by
-- proof
  apply StatMech.mem_downCompress i 𝒜 ω

/--
[lowerCoord_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma lowerCoord_self_eq
  [DecidableEq E]
  {i : E}
  {ω : ConfigSpace E} :
-- imply
  lowerCoord i ω i = false := by
-- proof
  apply StatMech.lowerCoord_self i ω

/--
[lowerCoord_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma lowerCoord_of_ne_eq
  [DecidableEq E]
  {i j : E}
  {ω : ConfigSpace E}
-- given
  (h : j ≠ i) :
-- imply
  lowerCoord i ω j = ω j := by
-- proof
  apply StatMech.lowerCoord_of_ne h ω

/--
[cfgSupport_lowerCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma cfgSupport_lowerCoord_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {ω : ConfigSpace E} :
-- imply
  cfgSupport (lowerCoord i ω) = (cfgSupport ω).erase i := by
-- proof
  apply StatMech.cfgSupport_lowerCoord i ω

/--
[downCompress_isDownAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma downCompress_isDownAt_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω ∈ downCompress i 𝒜) :
-- imply
  lowerCoord i ω ∈ downCompress i 𝒜 := by
-- proof
  apply StatMech.downCompress_isDownAt i 𝒜 hω

/--
[downCompress_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma downCompress_idem_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)} :
-- imply
  downCompress i (downCompress i 𝒜) = downCompress i 𝒜 := by
-- proof
  apply StatMech.downCompress_idem i 𝒜

/--
[occursOn_univ_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma occursOn_univ_iff_eq
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  OccursOn A Set.univ ω ↔ ω ∈ A := by
-- proof
  apply StatMech.occursOn_univ_iff A ω

/--
[occursOn_empty_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma occursOn_empty_iff_eq
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  OccursOn A (∅ : Set E) ω ↔ ∀ ω', ω' ∈ A := by
-- proof
  apply StatMech.occursOn_empty_iff A ω

/--
[fin1_coord_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma fin1_coord_cases_eq
  {K : Set (Fin 1)} :
-- imply
  K = ∅ ∨ K = Set.univ := by
-- proof
  apply StatMech.fin1_coord_cases K

/--
[mem_disjointOccurrence_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma mem_disjointOccurrence_fin1_eq
  {A B : Set (ConfigSpace (Fin 1))}
  {ω : ConfigSpace (Fin 1)} :
-- imply
  ω ∈ disjointOccurrence A B ↔ ((∀ ω', ω' ∈ A) ∧ ω ∈ B) ∨ (ω ∈ A ∧ (∀ ω', ω' ∈ B)) := by
-- proof
  apply StatMech.mem_disjointOccurrence_fin1 A B ω

/--
[forall_mem_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma forall_mem_fin1_eq
  {A : Set (ConfigSpace (Fin 1))} :
-- imply
  (∀ ω', ω' ∈ A) ↔ ((fun _ => false) ∈ A ∧ (fun _ => true) ∈ A) := by
-- proof
  apply StatMech.forall_mem_fin1 A

/--
[pweight_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma pweight_fin1_eq
  {φ : Fin 1 → Bool → ℝ}
  {ω : ConfigSpace (Fin 1)} :
-- imply
  pweight φ ω = φ 0 (ω 0) := by
-- proof
  apply StatMech.pweight_fin1 φ ω

/--
[wprob_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma wprob_fin1_eq
  {φ : Fin 1 → Bool → ℝ}
  {S : Set (ConfigSpace (Fin 1))} :
-- imply
  wprob φ S = S.indicator (fun _ => (1 : ℝ)) (fun _ => false) * φ 0 false + S.indicator (fun _ => (1 : ℝ)) (fun _ => true) * φ 0 true := by
-- proof
  apply StatMech.wprob_fin1 φ S

/--
[reimer_wprob_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma reimer_wprob_one_eq
  {φ : Fin 1 → Bool → ℝ}
  {A B : Set (ConfigSpace (Fin 1))}
-- given
  (hφ0 : ∀ i b, 0 ≤ φ i b)
  (hφ1 : ∀ i, φ i false + φ i true = 1) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.reimer_wprob_one φ hφ0 hφ1 A B

/--
[DependsOn.mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma mono_eq
  {A : Set (ConfigSpace E)}
  {S S' : Set E}
-- given
  (h : DependsOn A S)
  (hSS' : S ⊆ S') :
-- imply
  DependsOn A S' := by
-- proof
  apply StatMech.DependsOn.mono h hSS'

/--
[DependsOn.occursOn_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma occursOn_iff_eq
  {A : Set (ConfigSpace E)}
  {S : Set E}
  {ω : ConfigSpace E}
-- given
  (h : DependsOn A S) :
-- imply
  OccursOn A S ω ↔ ω ∈ A := by
-- proof
  apply StatMech.DependsOn.occursOn_iff h ω

/--
[disjointOccurrence_eq_inter_of_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma disjointOccurrence_eq_inter_of_dependsOn_eq
  {A B : Set (ConfigSpace E)}
  {S T : Set E}
-- given
  (hA : DependsOn A S)
  (hB : DependsOn B T)
  (hST : Disjoint S T) :
-- imply
  disjointOccurrence A B = A ∩ B := by
-- proof
  apply StatMech.disjointOccurrence_eq_inter_of_dependsOn hA hB hST

/--
[pweight_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma pweight_split_eq
  [Fintype E]
  [DecidablePred P]
  {φ : E → Bool → ℝ}
  {a : {x // P x} → Bool}
  {b : {x // ¬ P x} → Bool}
-- given
  (P : E → Prop) :
-- imply
  pweight φ ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b)) = (∏ i : {x // P x}, φ i (a i)) * (∏ i : {x // ¬ P x}, φ i (b i)) := by
-- proof
  apply StatMech.pweight_split P φ a b

/--
[wprob_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma wprob_reindex_eq
  [Fintype E]
  [DecidableEq E]
  [DecidablePred P]
  {φ : E → Bool → ℝ}
  {S : Set (ConfigSpace E)}
-- given
  (P : E → Prop) :
-- imply
  wprob φ S = ∑ a : {x // P x} → Bool, ∑ b : {x // ¬ P x} → Bool, S.indicator (fun _ => (1 : ℝ)) ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b)) * pweight φ ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b)) := by
-- proof
  apply StatMech.wprob_reindex P φ S

/--
[indicator_indep_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma indicator_indep_compl_eq
  {A : Set (ConfigSpace E)}
  [DecidablePred P]
  {a : {x // P x} → Bool}
  {b b' : {x // ¬ P x} → Bool}
-- given
  (P : E → Prop)
  (hA : DependsOn A {x | P x}) :
-- imply
  A.indicator (fun _ => (1 : ℝ)) ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b)) = A.indicator (fun _ => (1 : ℝ)) ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b')) := by
-- proof
  apply StatMech.indicator_indep_compl P hA a b b'

/--
[indicator_indep_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma indicator_indep_pred_eq
  {B : Set (ConfigSpace E)}
  [DecidablePred P]
  {a a' : {x // P x} → Bool}
  {b : {x // ¬ P x} → Bool}
-- given
  (P : E → Prop)
  (hB : DependsOn B {x | ¬ P x}) :
-- imply
  B.indicator (fun _ => (1 : ℝ)) ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b)) = B.indicator (fun _ => (1 : ℝ)) ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a', b)) := by
-- proof
  apply StatMech.indicator_indep_pred P hB a a' b

/--
[sum_prod_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma sum_prod_eq_one_eq
  [Fintype S]
  [DecidableEq S]
  {ψ : S → Bool → ℝ}
-- given
  (h : ∀ s, ψ s false + ψ s true = 1) :
-- imply
  (∑ a : S → Bool, ∏ s, ψ s (a s)) = 1 := by
-- proof
  apply StatMech.sum_prod_eq_one ψ h

/--
[wprob_inter_mul_of_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma wprob_inter_mul_of_split_eq
  [Fintype E]
  [DecidableEq E]
  [DecidablePred P]
  {φ : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (P : E → Prop)
  (hφ1 : ∀ x, φ x false + φ x true = 1)
  (hA : DependsOn A {x | P x})
  (hB : DependsOn B {x | ¬ P x}) :
-- imply
  wprob φ (A ∩ B) = wprob φ A * wprob φ B := by
-- proof
  apply StatMech.wprob_inter_mul_of_split P φ hφ1 hA hB

/--
[reimer_wprob_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean)
-/
@[path]
private lemma reimer_wprob_of_disjoint_support_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
  {S T : Set E}
-- given
  (hφ1 : ∀ x, φ x false + φ x true = 1)
  (hA : DependsOn A S)
  (hB : DependsOn B T)
  (hST : Disjoint S T) :
-- imply
  wprob φ (disjointOccurrence A B) = wprob φ A * wprob φ B := by
-- proof
  apply StatMech.reimer_wprob_of_disjoint_support φ hφ1 hA hB hST


-- created on 2026-10-23
