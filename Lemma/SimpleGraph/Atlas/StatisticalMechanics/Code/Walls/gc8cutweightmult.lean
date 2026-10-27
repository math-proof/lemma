import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc8cutweightmult
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc8_not_internal_both_cwm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutweightmult.lean)
-/
@[path]
private lemma gc8_not_internal_both_cwm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {e : Sym2 V} :
-- imply
  ¬ (acwInternal S e ∧ acwInternal Sᶜ e) := by
-- proof
  apply StatMech.Walls.gc8_not_internal_both_cwm G S e

/--
[gc8_notInternalS_iff_internalCompl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutweightmult.lean)
-/
@[path]
private lemma gc8_notInternalS_iff_internalCompl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {e : Sym2 V}
-- given
  (hcut : acwClosedCut G S)
  (he : e ∈ G.edgeFinset) :
-- imply
  ¬ acwInternal S e ↔ acwInternal Sᶜ e := by
-- proof
  apply StatMech.Walls.gc8_notInternalS_iff_internalCompl G S hcut he

/--
[gc8_cut_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutweightmult.lean)
-/
@[path]
private lemma gc8_cut_decomp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Sharpness.Current V}
  {e : Sym2 V}
-- given
  (hcut : acwClosedCut G S)
  (he : e ∈ G.edgeFinset) :
-- imply
  n e = acwRestrict (acwInternal S) n e + acwRestrict (acwInternal Sᶜ) n e := by
-- proof
  apply StatMech.Walls.gc8_cut_decomp G S hcut n he

/--
[gc8_notInternalS_weight_eq_internalCompl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutweightmult.lean)
-/
@[path]
private lemma gc8_notInternalS_weight_eq_internalCompl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {n : Sharpness.Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  weight G β J (acwRestrict (fun e => ¬ acwInternal S e) n) = weight G β J (acwRestrict (acwInternal Sᶜ) n) := by
-- proof
  apply StatMech.Walls.gc8_notInternalS_weight_eq_internalCompl G β J S hcut n

/--
[gc8_cutWeight_mult](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutweightmult.lean)
-/
@[path]
private lemma gc8_cutWeight_mult_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {n : Sharpness.Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  weight G β J n = weight G β J (acwRestrict (acwInternal Sᶜ) n) * weight G β J (acwRestrict (acwInternal S) n) := by
-- proof
  apply StatMech.Walls.gc8_cutWeight_mult G β J S hcut n

/--
[gc8_cutWeight_mult_innerFirst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutweightmult.lean)
-/
@[path]
private lemma gc8_cutWeight_mult_innerFirst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {n : Sharpness.Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  weight G β J n = weight G β J (acwRestrict (acwInternal S) n) * weight G β J (acwRestrict (acwInternal Sᶜ) n) := by
-- proof
  apply StatMech.Walls.gc8_cutWeight_mult_innerFirst G β J S hcut n

/--
[gc8_cut_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutweightmult.lean)
-/
@[path]
private lemma gc8_cut_support_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Sharpness.Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  Sharpness.sources G (acwRestrict (acwInternal S) n) = (Sharpness.sources G n) ∩ S := by
-- proof
  apply StatMech.Walls.gc8_cut_support G S hcut n

/--
[gc8_cut_support_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutweightmult.lean)
-/
@[path]
private lemma gc8_cut_support_external_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Sharpness.Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n) = (Sharpness.sources G n) ∩ Sᶜ := by
-- proof
  apply StatMech.Walls.gc8_cut_support_external G S hcut n

/--
[gc8_weight_factor_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutweightmult.lean)
-/
@[path]
private lemma gc8_weight_factor_pred_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  [DecidablePred p]
  {n : Sharpness.Current V}
-- given
  (p : Sym2 V → Prop) :
-- imply
  weight G β J n = weight G β J (acwRestrict p n) * weight G β J (acwRestrict (fun e => ¬ p e) n) := by
-- proof
  apply StatMech.Walls.gc8_weight_factor_pred G β J p n

/--
[gc8_cutWeight_mult_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutweightmult.lean)
-/
@[path]
private lemma gc8_cutWeight_mult_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {n : Sharpness.Current V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ weight G β J (acwRestrict (acwInternal Sᶜ) n) ∧ 0 ≤ weight G β J (acwRestrict (acwInternal S) n) := by
-- proof
  apply StatMech.Walls.gc8_cutWeight_mult_nonneg G β J hβ hJ S n

/--
[gc8_closedCut_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutweightmult.lean)
-/
@[path]
private lemma gc8_closedCut_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  acwClosedCut G (∅ : Finset V) := by
-- proof
  apply StatMech.Walls.gc8_closedCut_empty G

/--
[gc8_cutWeight_mult_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutweightmult.lean)
-/
@[path]
private lemma gc8_cutWeight_mult_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Sharpness.Current (Fin 3)} :
-- imply
  weight (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) n = weight (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) (acwRestrict (acwInternal (∅ : Finset (Fin 3))ᶜ) n) * weight (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) (acwRestrict (acwInternal (∅ : Finset (Fin 3))) n) := by
-- proof
  apply StatMech.Walls.gc8_cutWeight_mult_nonvacuous G n


-- created on 2026-10-23
