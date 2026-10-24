import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.FSClose
open Finset Real StatMech StatMech.Probability


/--
[fsc2_perCoord_lsi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_perCoord_lsi_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {G : ConfigSpace E → ℝ}
  {e : E}
  {ω : ConfigSpace E}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  esd_entCoord p (fun ω => (G ω) ^ 2) e ω ≤ (G (StatMech.setOpen e ω) - G (StatMech.setClosed e ω)) ^ 2 := by
-- proof
  apply StatMech.Probability.fsc2_perCoord_lsi hp0 hp1 G e ω

/--
[fsc2_dirichlet_fourier_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_dirichlet_fourier_coord_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {G : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (G (StatMech.setOpen e ω) - G (StatMech.setClosed e ω)) ^ 2) = (1 / (ptn_sigma p) ^ 2) * ∑ S ∈ univ.filter (fun S : Finset E => e ∈ S), (ptn_coeff p G S) ^ 2 := by
-- proof
  apply StatMech.Probability.fsc2_dirichlet_fourier_coord hp0 hp1 G e

/--
[fsc2_dirichlet_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_dirichlet_fourier_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {G : ConfigSpace E → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ e : E, OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (G (StatMech.setOpen e ω) - G (StatMech.setClosed e ω)) ^ 2)) = (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset E, (S.card : ℝ) * (ptn_coeff p G S) ^ 2 := by
-- proof
  apply StatMech.Probability.fsc2_dirichlet_fourier hp0 hp1 G

/--
[fsc2_reindex_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_reindex_setOpen_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype κ]
  [DecidableEq κ]
  {σ : κ ≃ E}
  {e' : κ}
  {ω : ConfigSpace κ} :
-- imply
  (fun i : E => StatMech.setOpen e' ω (σ.symm i)) = StatMech.setOpen (σ e') (fun i : E => ω (σ.symm i)) := by
-- proof
  apply StatMech.Probability.fsc2_reindex_setOpen σ e' ω

/--
[fsc2_reindex_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_reindex_setClosed_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype κ]
  [DecidableEq κ]
  {σ : κ ≃ E}
  {e' : κ}
  {ω : ConfigSpace κ} :
-- imply
  (fun i : E => StatMech.setClosed e' ω (σ.symm i)) = StatMech.setClosed (σ e') (fun i : E => ω (σ.symm i)) := by
-- proof
  apply StatMech.Probability.fsc2_reindex_setClosed σ e' ω

/--
[fsc2_deriv_sq_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_deriv_sq_reindex_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype κ]
  [DecidableEq κ]
  {σ : κ ≃ E}
  {G : ConfigSpace E → ℝ}
  {e' : κ} :
-- imply
  (fun ω : ConfigSpace κ => (ptn_reindex σ G (StatMech.setOpen e' ω) - ptn_reindex σ G (StatMech.setClosed e' ω)) ^ 2) = ptn_reindex σ (fun x => (G (StatMech.setOpen (σ e') x) - G (StatMech.setClosed (σ e') x)) ^ 2) := by
-- proof
  apply StatMech.Probability.fsc2_deriv_sq_reindex σ G e'

/--
[fsc2_dirichlet_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_dirichlet_reindex_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype κ]
  [DecidableEq κ]
  {σ : κ ≃ E}
  {p : ℝ}
  {G : ConfigSpace E → ℝ} :
-- imply
  (∑ e' : κ, OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (ptn_reindex σ G (StatMech.setOpen e' ω) - ptn_reindex σ G (StatMech.setClosed e' ω)) ^ 2)) = ∑ e : E, OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (G (StatMech.setOpen e ω) - G (StatMech.setClosed e ω)) ^ 2) := by
-- proof
  apply StatMech.Probability.fsc2_dirichlet_reindex σ p G

/--
[fsc2_ent_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_ent_reindex_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype κ]
  [DecidableEq κ]
  {σ : κ ≃ E}
  {p : ℝ}
  {G : ConfigSpace E → ℝ} :
-- imply
  esd_ent (OSSS.bernoulliWeight p) (fun ω => (ptn_reindex σ G ω) ^ 2) = esd_ent (OSSS.bernoulliWeight p) (fun ω => (G ω) ^ 2) := by
-- proof
  apply StatMech.Probability.fsc2_ent_reindex σ p G

/--
[fsc2_globalLSI](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_globalLSI_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {G : ConfigSpace E → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  esd_ent (OSSS.bernoulliWeight p) (fun ω => (G ω) ^ 2) ≤ ∑ e : E, OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (G (StatMech.setOpen e ω) - G (StatMech.setClosed e ω)) ^ 2) := by
-- proof
  apply StatMech.Probability.fsc2_globalLSI hp0 hp1 G

/--
[fsc2_lsi_spectral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_lsi_spectral_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {G : ConfigSpace E → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  esd_ent (OSSS.bernoulliWeight p) (fun ω => (G ω) ^ 2) ≤ (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset E, (S.card : ℝ) * (ptn_coeff p G S) ^ 2 := by
-- proof
  apply StatMech.Probability.fsc2_lsi_spectral hp0 hp1 G

/--
[fsc2_coeff_noiseOp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_coeff_noiseOp_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {ρ : ℝ}
  {f : ConfigSpace E → ℝ}
  {S : Finset E}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ptn_coeff p (ptn_noiseOp p ρ f) S = ρ ^ S.card * ptn_coeff p f S := by
-- proof
  apply StatMech.Probability.fsc2_coeff_noiseOp hp0 hp1 ρ f S

/--
[fsc2_lsi_spectral_noiseOp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_lsi_spectral_noiseOp_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {ρ : ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  esd_ent (OSSS.bernoulliWeight p) (fun ω => (ptn_noiseOp p ρ f ω) ^ 2) ≤ (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset E, (S.card : ℝ) * ((ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2) := by
-- proof
  apply StatMech.Probability.fsc2_lsi_spectral_noiseOp hp0 hp1 ρ f

/--
[fsc2_entMassFamily_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_entMassFamily_holds_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  fsc2_EntMassFamily p φ := by
-- proof
  apply StatMech.Probability.fsc2_entMassFamily_holds hp0 hp1 φ

/--
[fsc2_dampingHard_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_dampingHard_of_residue_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
  {H : fsc2_DampingHardResidue q} :
-- imply
  esa_DampingHard q := by
-- proof
  apply StatMech.Probability.fsc2_dampingHard_of_residue H

/--
[fsc2_dampingWitness_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_dampingWitness_of_residue_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
  {H : fsc2_DampingHardResidue q} :
-- imply
  pen_DampingWitness q := by
-- proof
  apply StatMech.Probability.fsc2_dampingWitness_of_residue H

/--
[fsc2_rhoOptimise_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_rhoOptimise_of_residue_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
  {H : fsc2_DampingHardResidue q} :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.fsc2_rhoOptimise_of_residue H

/--
[fsc2_PBiasedHC_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_PBiasedHC_of_residue_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
  {H : fsc2_DampingHardResidue q}
-- given
  (hq : q ≤ 1) :
-- imply
  kpb_PBiasedHC q := by
-- proof
  apply StatMech.Probability.fsc2_PBiasedHC_of_residue hq H

/--
[fsc2_residue_nonvac](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_residue_nonvac_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  fsc2_EntMassFamily p φ := by
-- proof
  apply StatMech.Probability.fsc2_residue_nonvac hp0 hp1 φ

/--
[fsc2_residue_noncirc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean)
-/
@[path]
private lemma fsc2_residue_noncirc_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
  {H : fsc2_DampingHardResidue q}
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1)
  (hVar : 0 < OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
  (hδpos : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
  (hδsmall : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) < Real.exp (-(1 / (2 * (p * (1 - p))))))
  (hfam : fsc2_EntMassFamily p φ) :
-- imply
  pen_dampedMass p (Real.exp (-(1 / (2 * (p * (1 - p)))))) (fun ω => if φ ω then (1 : ℝ) else 0) ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.fsc2_residue_noncirc H hp hp1 φ hVar hδpos hδsmall hfam


-- created on 2026-10-23
