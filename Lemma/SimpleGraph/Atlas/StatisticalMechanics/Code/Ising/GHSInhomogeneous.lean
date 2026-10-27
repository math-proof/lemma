import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
open Finset SimpleGraph Set StatMech StatMech.Ising


/--
[ghsi_fieldSum_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_fieldSum_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {sigma : V ≃ W}
  {omega : ConfigSpace W}
-- given
  (hfV : V → ℝ)
  (hfW : W → ℝ)
  (hhf : ∀ x, hfV x = hfW (sigma x)) :
-- imply
  (∑ x : V, hfV x * spin (isingCfgEquiv sigma omega) x) = ∑ y : W, hfW y * spin omega y := by
-- proof
  apply StatMech.Ising.ghsi_fieldSum_relabel G H sigma hfV hfW hhf omega

/--
[ghsi_wJ_const_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_wJ_const_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {sigma : V ≃ W}
  {beta : ℝ}
  {omega : ConfigSpace W}
-- given
  (hsigma : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
  (hfV : V → ℝ)
  (hfW : W → ℝ)
  (hhf : ∀ x, hfV x = hfW (sigma x)) :
-- imply
  wJ G.edgeFinset (fun _ => beta) hfV (isingCfgEquiv sigma omega) = wJ H.edgeFinset (fun _ => beta) hfW omega := by
-- proof
  apply StatMech.Ising.ghsi_wJ_const_relabel G H sigma hsigma beta hfV hfW hhf omega

/--
[ghsi_ZJ_const_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_ZJ_const_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {sigma : V ≃ W}
  {beta : ℝ}
-- given
  (hsigma : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
  (hfV : V → ℝ)
  (hfW : W → ℝ)
  (hhf : ∀ x, hfV x = hfW (sigma x)) :
-- imply
  ZJ G.edgeFinset (fun _ => beta) hfV = ZJ H.edgeFinset (fun _ => beta) hfW := by
-- proof
  apply StatMech.Ising.ghsi_ZJ_const_relabel G H sigma hsigma beta hfV hfW hhf

/--
[ghsi_expJ_spin_const_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_expJ_spin_const_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {sigma : V ≃ W}
  {beta : ℝ}
  {x : V}
-- given
  (hsigma : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
  (hfV : V → ℝ)
  (hfW : W → ℝ)
  (hhf : ∀ x, hfV x = hfW (sigma x)) :
-- imply
  expJ G.edgeFinset (fun _ => beta) hfV (fun omega => spin omega x) = expJ H.edgeFinset (fun _ => beta) hfW (fun omega => spin omega (sigma x)) := by
-- proof
  apply StatMech.Ising.ghsi_expJ_spin_const_relabel G H sigma hsigma beta hfV hfW hhf x

/--
[ghsi_wJ_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_wJ_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {beta : ℝ}
  {s : ConfigSpace V}
  {t : ConfigSpace W}
-- given
  (hfV : V → ℝ)
  (hfW : W → ℝ) :
-- imply
  wJ (G ⊕g H).edgeFinset (fun _ => beta) (Sum.elim hfV hfW) (isingSumConfigEquiv.symm (s, t)) = wJ G.edgeFinset (fun _ => beta) hfV s * wJ H.edgeFinset (fun _ => beta) hfW t := by
-- proof
  apply StatMech.Ising.ghsi_wJ_sum G H beta hfV hfW s t

/--
[ghsi_ZJ_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_ZJ_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {beta : ℝ}
-- given
  (hfV : V → ℝ)
  (hfW : W → ℝ) :
-- imply
  ZJ (G ⊕g H).edgeFinset (fun _ => beta) (Sum.elim hfV hfW) = ZJ G.edgeFinset (fun _ => beta) hfV * ZJ H.edgeFinset (fun _ => beta) hfW := by
-- proof
  apply StatMech.Ising.ghsi_ZJ_sum G H beta hfV hfW

/--
[ghsi_expJ_spin_sum_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_expJ_spin_sum_inl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {beta : ℝ}
  {x : V}
-- given
  (hfV : V → ℝ)
  (hfW : W → ℝ) :
-- imply
  expJ (G ⊕g H).edgeFinset (fun _ => beta) (Sum.elim hfV hfW) (fun s => spin s (Sum.inl x)) = expJ G.edgeFinset (fun _ => beta) hfV (fun s => spin s x) := by
-- proof
  apply StatMech.Ising.ghsi_expJ_spin_sum_inl G H beta hfV hfW x

/--
[ghsiExp2_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiExp2_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {f g : ConfigSpace V → ℝ}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiExp2 G K hf (fun a b => f a * g b) = expJ G.edgeFinset K hf f * expJ G.edgeFinset K hf g := by
-- proof
  apply StatMech.Ising.ghsiExp2_factor G K hf f g

/--
[ghsi_bondSum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_bondSum_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {q a : ConfigSpace V} :
-- imply
  (∑ e ∈ G.edgeFinset, K e * bond a e) + ∑ e ∈ G.edgeFinset, K e * bond (ghsLMate q a) e = (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q), (2 * K e) * bond a e) + ∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ, (2 * K e) * bond a e := by
-- proof
  apply StatMech.Ising.ghsi_bondSum_split G K q a

/--
[ghsi_fieldSum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_fieldSum_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  (∑ v : V, hf v * spin a v) + ∑ v : V, hf v * spin (ghsLMate q a) v = ∑ v ∈ ghsLAgreeFinset q, (2 * hf v) * spin a v := by
-- proof
  apply StatMech.Ising.ghsi_fieldSum_split G hf q a

/--
[ghsi_duplicateWeight_eq_tWeight_mul_uWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_duplicateWeight_eq_tWeight_mul_uWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {q a : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf (ghsLMate q a) = ghsiTWeight G K hf q a * ghsiUWeight G K q a := by
-- proof
  apply StatMech.Ising.ghsi_duplicateWeight_eq_tWeight_mul_uWeight G K hf q a

/--
[ghsiTWeight_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiTWeight_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {q a : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiTWeight G K hf q a = ghsiTWeight G K hf q (ghsLTComplete q (ghsLSplitEquiv q a).1) := by
-- proof
  apply StatMech.Ising.ghsiTWeight_split G K hf q a

/--
[ghsiUWeight_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiUWeight_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {q a : ConfigSpace V} :
-- imply
  ghsiUWeight G K q a = ghsiUWeight G K q (ghsLUComplete q (ghsLSplitEquiv q a).2) := by
-- proof
  apply StatMech.Ising.ghsiUWeight_split G K q a

/--
[ghsiTWeight_eq_wJ_restricted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiTWeight_eq_wJ_restricted_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {q a : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiTWeight G K hf q a = wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)) (fun e => 2 * K e) (fun x => if x ∈ ghsLAgreeFinset q then 2 * hf x else 0) a := by
-- proof
  apply StatMech.Ising.ghsiTWeight_eq_wJ_restricted G K hf q a

/--
[ghsiUWeight_eq_wJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiUWeight_eq_wJ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {q a : ConfigSpace V} :
-- imply
  ghsiUWeight G K q a = wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ) (fun e => 2 * K e) (fun _ => 0) a := by
-- proof
  apply StatMech.Ising.ghsiUWeight_eq_wJ G K q a

/--
[ghsiFibreWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiFibreWeight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {q a : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  0 < ghsiFibreWeight G K hf q a := by
-- proof
  apply StatMech.Ising.ghsiFibreWeight_pos G K hf q a

/--
[ghsiFibreMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiFibreMass_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {q : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  0 < ghsiFibreMass G K hf q := by
-- proof
  apply StatMech.Ising.ghsiFibreMass_pos G K hf q

/--
[ghsiAgreementProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiAgreementProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
-- given
  (hf : V → ℝ) :
-- imply
  0 ≤ ghsiAgreementProb G K hf := by
-- proof
  apply StatMech.Ising.ghsiAgreementProb_nonneg G K hf

/--
[ghsiAgreementProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiAgreementProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
-- given
  (hf : V → ℝ) :
-- imply
  ∑ q : ConfigSpace V, ghsiAgreementProb G K hf q = 1 := by
-- proof
  apply StatMech.Ising.ghsiAgreementProb_sum_eq_one G K hf

/--
[ghsiAgreementProb_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiAgreementProb_fkg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
-- given
  (hf : V → ℝ)
  (hK : ∀ e, 0 ≤ K e)
  (hhf : ∀ x, 0 ≤ hf x) :
-- imply
  FKGLatticeCondition (ghsiAgreementProb G K hf) := by
-- proof
  apply StatMech.Ising.ghsiAgreementProb_fkg G K hf hK hhf

/--
[ghsiUWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiUWeight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {q a : ConfigSpace V} :
-- imply
  0 < ghsiUWeight G K q a := by
-- proof
  apply StatMech.Ising.ghsiUWeight_pos G K q a

/--
[ghsiTWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiTWeight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {q a : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  0 < ghsiTWeight G K hf q a := by
-- proof
  apply StatMech.Ising.ghsiTWeight_pos G K hf q a

/--
[ghsiFibreUU_eq_uExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiFibreUU_eq_uExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {o x : V}
  {q : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiFibreUU G K hf o x q = ghsiUExpectation G K q (fun a => uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x) := by
-- proof
  apply StatMech.Ising.ghsiFibreUU_eq_uExpectation G K hf o x q

/--
[ghsiFibreT_eq_tExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiFibreT_eq_tExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {y : V}
  {q : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiFibreT G K hf y q = ghsiTExpectation G K hf q (fun a => tvar a (ghsLMate q a) y) := by
-- proof
  apply StatMech.Ising.ghsiFibreT_eq_tExpectation G K hf y q

/--
[ghsiDisagreementCorr_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiDisagreementCorr_antitone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {o x : V}
-- given
  (hK : ∀ e, 0 ≤ K e) :
-- imply
  Antitone (ghsiDisagreementCorr G K o x) := by
-- proof
  apply StatMech.Ising.ghsiDisagreementCorr_antitone G K hK o x

/--
[ghsiAgreementMag_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiAgreementMag_monotone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {y : V}
-- given
  (hf : V → ℝ)
  (hK : ∀ e, 0 ≤ K e)
  (hhf : ∀ x, 0 ≤ hf x) :
-- imply
  Monotone (ghsiAgreementMag G K hf y) := by
-- proof
  apply StatMech.Ising.ghsiAgreementMag_monotone G K hf hK hhf y

/--
[ghsiFibreUU_eq_disagreementCorr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiFibreUU_eq_disagreementCorr_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {o x : V}
  {q : ConfigSpace V}
-- given
  (hf : V → ℝ)
  (hox : o ≠ x) :
-- imply
  ghsiFibreUU G K hf o x q = ghsiDisagreementCorr G K o x (ghsLAgreeFinset q) := by
-- proof
  apply StatMech.Ising.ghsiFibreUU_eq_disagreementCorr G K hf o x hox q

/--
[ghsiOutFieldWeight_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiOutFieldWeight_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiOutFieldWeight hf q a = ghsiOutFieldWeight hf q (ghsLUComplete q (ghsLSplitEquiv q a).2) := by
-- proof
  apply StatMech.Ising.ghsiOutFieldWeight_split G hf q a

/--
[ghsi_wJ_field_eq_tWeight_mul_out](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_wJ_field_eq_tWeight_mul_out_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {q a : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)) (fun e => 2 * K e) (fun x => 2 * hf x) a = ghsiTWeight G K hf q a * ghsiOutFieldWeight hf q a := by
-- proof
  apply StatMech.Ising.ghsi_wJ_field_eq_tWeight_mul_out G K hf q a

/--
[ghsiFibreT_eq_agreementMag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiFibreT_eq_agreementMag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {y : V}
  {q : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiFibreT G K hf y q = ghsiAgreementMag G K hf y (ghsLAgreeFinset q) := by
-- proof
  apply StatMech.Ising.ghsiFibreT_eq_agreementMag G K hf y q

/--
[ghsiExp2_fibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiExp2_fibre_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {F : ConfigSpace V → ConfigSpace V → ℝ}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiExp2 G K hf F = ∑ q : ConfigSpace V, ghsiAgreementProb G K hf q * ghsiFibreExpectation G K hf F q := by
-- proof
  apply StatMech.Ising.ghsiExp2_fibre G K hf F

/--
[ghsi_fibreFactorization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_fibreFactorization_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {o x y : V}
  {q : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiFibreExpectation G K hf (fun a b => uvar a b o * uvar a b x * tvar a b y) q = ghsiFibreUU G K hf o x q * ghsiFibreT G K hf y q := by
-- proof
  apply StatMech.Ising.ghsi_fibreFactorization G K hf o x y q

/--
[ghsi_duplicate_cov_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_duplicate_cov_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {o x y : V}
-- given
  (hf : V → ℝ)
  (hK : ∀ e, 0 ≤ K e)
  (hhf : ∀ x, 0 ≤ hf x)
  (hox : o ≠ x) :
-- imply
  ghsiExp2 G K hf (fun a b => uvar a b o * uvar a b x * tvar a b y) ≤ ghsiExp2 G K hf (fun a b => uvar a b o * uvar a b x) * ghsiExp2 G K hf (fun a b => tvar a b y) := by
-- proof
  apply StatMech.Ising.ghsi_duplicate_cov_nonpos G K hf hK hhf o x y hox

/--
[ghsiExp2_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiExp2_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {F H : ConfigSpace V → ConfigSpace V → ℝ}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiExp2 G K hf (fun a b => F a b + H a b) = ghsiExp2 G K hf F + ghsiExp2 G K hf H := by
-- proof
  apply StatMech.Ising.ghsiExp2_add G K hf F H

/--
[ghsiExp2_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiExp2_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {c : ℝ}
  {F : ConfigSpace V → ConfigSpace V → ℝ}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiExp2 G K hf (fun a b => c * F a b) = c * ghsiExp2 G K hf F := by
-- proof
  apply StatMech.Ising.ghsiExp2_const_mul G K hf c F

/--
[expJ_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma expJ_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
-- given
  (hf : V → ℝ) :
-- imply
  expJ G.edgeFinset K hf (fun _ => (1 : ℝ)) = 1 := by
-- proof
  apply StatMech.Ising.expJ_one G K hf

/--
[ghsiExp2_factor_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiExp2_factor_a_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {f : ConfigSpace V → ℝ}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiExp2 G K hf (fun a _ => f a) = expJ G.edgeFinset K hf f := by
-- proof
  apply StatMech.Ising.ghsiExp2_factor_a G K hf f

/--
[ghsiExp2_factor_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiExp2_factor_b_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {f : ConfigSpace V → ℝ}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiExp2 G K hf (fun _ b => f b) = expJ G.edgeFinset K hf f := by
-- proof
  apply StatMech.Ising.ghsiExp2_factor_b G K hf f

/--
[ghsi_ursell_eq_four_duplicate_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_ursell_eq_four_duplicate_cov_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {o x y : V}
-- given
  (hf : V → ℝ) :
-- imply
  expJ G.edgeFinset K hf (fun s => spin s o * (spin s x * spin s y)) - expJ G.edgeFinset K hf (fun s => spin s o) * expJ G.edgeFinset K hf (fun s => spin s x * spin s y) - expJ G.edgeFinset K hf (fun s => spin s o * spin s x) * expJ G.edgeFinset K hf (fun s => spin s y) - expJ G.edgeFinset K hf (fun s => spin s o * spin s y) * expJ G.edgeFinset K hf (fun s => spin s x) + 2 * expJ G.edgeFinset K hf (fun s => spin s o) * expJ G.edgeFinset K hf (fun s => spin s x) * expJ G.edgeFinset K hf (fun s => spin s y) = 4 * (ghsiExp2 G K hf (fun a b => uvar a b o * uvar a b x * tvar a b y) - ghsiExp2 G K hf (fun a b => uvar a b o * uvar a b x) * ghsiExp2 G K hf (fun a b => tvar a b y)) := by
-- proof
  apply StatMech.Ising.ghsi_ursell_eq_four_duplicate_cov G K hf o x y

/--
[ghsi_ursell_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_ursell_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {o x y : V}
-- given
  (hf : V → ℝ)
  (hK : ∀ e, 0 ≤ K e)
  (hhf : ∀ x, 0 ≤ hf x)
  (hox : o ≠ x) :
-- imply
  expJ G.edgeFinset K hf (fun s => spin s o * (spin s x * spin s y)) - expJ G.edgeFinset K hf (fun s => spin s o) * expJ G.edgeFinset K hf (fun s => spin s x * spin s y) - expJ G.edgeFinset K hf (fun s => spin s o * spin s x) * expJ G.edgeFinset K hf (fun s => spin s y) - expJ G.edgeFinset K hf (fun s => spin s o * spin s y) * expJ G.edgeFinset K hf (fun s => spin s x) + 2 * expJ G.edgeFinset K hf (fun s => spin s o) * expJ G.edgeFinset K hf (fun s => spin s x) * expJ G.edgeFinset K hf (fun s => spin s y) ≤ 0 := by
-- proof
  apply StatMech.Ising.ghsi_ursell_nonpos G K hf hK hhf o x y hox

/--
[ghsi_hasDerivAt_wJ_fieldLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_hasDerivAt_wJ_fieldLine_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {s : ConfigSpace V}
  {t : ℝ}
-- given
  (hf dir : V → ℝ) :
-- imply
  HasDerivAt (fun u => wJ G.edgeFinset K (ghsiFieldLine hf dir u) s) (wJ G.edgeFinset K (ghsiFieldLine hf dir t) s * ghsiDirSpin dir s) t := by
-- proof
  apply StatMech.Ising.ghsi_hasDerivAt_wJ_fieldLine G K hf dir s t

/--
[ghsi_hasDerivAt_Z_fieldLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_hasDerivAt_Z_fieldLine_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {t : ℝ}
-- given
  (hf dir : V → ℝ) :
-- imply
  HasDerivAt (fun u => ZJ G.edgeFinset K (ghsiFieldLine hf dir u)) (∑ s : ConfigSpace V, wJ G.edgeFinset K (ghsiFieldLine hf dir t) s * ghsiDirSpin dir s) t := by
-- proof
  apply StatMech.Ising.ghsi_hasDerivAt_Z_fieldLine G K hf dir t

/--
[ghsi_hasDerivAt_num_fieldLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_hasDerivAt_num_fieldLine_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {f : ConfigSpace V → ℝ}
  {t : ℝ}
-- given
  (hf dir : V → ℝ) :
-- imply
  HasDerivAt (fun u => ∑ s : ConfigSpace V, f s * wJ G.edgeFinset K (ghsiFieldLine hf dir u) s) (∑ s : ConfigSpace V, f s * (wJ G.edgeFinset K (ghsiFieldLine hf dir t) s * ghsiDirSpin dir s)) t := by
-- proof
  apply StatMech.Ising.ghsi_hasDerivAt_num_fieldLine G K hf dir f t

/--
[ghsi_hasDerivAt_expectation_fieldLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_hasDerivAt_expectation_fieldLine_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {f : ConfigSpace V → ℝ}
  {t : ℝ}
-- given
  (hf dir : V → ℝ) :
-- imply
  HasDerivAt (fun u => expJ G.edgeFinset K (ghsiFieldLine hf dir u) f) (expJ G.edgeFinset K (ghsiFieldLine hf dir t) (fun s => f s * ghsiDirSpin dir s) - expJ G.edgeFinset K (ghsiFieldLine hf dir t) f * expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir)) t := by
-- proof
  apply StatMech.Ising.ghsi_hasDerivAt_expectation_fieldLine G K hf dir f t

/--
[ghsi_hasDerivAt_directionalCovariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_hasDerivAt_directionalCovariance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {f : ConfigSpace V → ℝ}
  {t : ℝ}
-- given
  (hf dir : V → ℝ) :
-- imply
  HasDerivAt (fun u => ghsiDirectionalCovariance G K (ghsiFieldLine hf dir u) dir f) (expJ G.edgeFinset K (ghsiFieldLine hf dir t) (fun s => f s * ghsiDirSpin dir s * ghsiDirSpin dir s) - expJ G.edgeFinset K (ghsiFieldLine hf dir t) (fun s => f s * ghsiDirSpin dir s) * expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir) - (expJ G.edgeFinset K (ghsiFieldLine hf dir t) (fun s => f s * ghsiDirSpin dir s) - expJ G.edgeFinset K (ghsiFieldLine hf dir t) f * expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir)) * expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir) - expJ G.edgeFinset K (ghsiFieldLine hf dir t) f * (expJ G.edgeFinset K (ghsiFieldLine hf dir t) (fun s => ghsiDirSpin dir s * ghsiDirSpin dir s) - expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir) * expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir))) t := by
-- proof
  apply StatMech.Ising.ghsi_hasDerivAt_directionalCovariance G K hf dir f t

/--
[ghsiUrsell3_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsiUrsell3_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {o x y : V}
-- given
  (hf : V → ℝ)
  (hK : ∀ e, 0 ≤ K e)
  (hhf : ∀ x, 0 ≤ hf x)
  (hox : o ≠ x) :
-- imply
  ghsiUrsell3 G K hf o x y ≤ 0 := by
-- proof
  apply StatMech.Ising.ghsiUrsell3_nonpos G K hf hK hhf o x y hox

/--
[ghsi_expJ_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_expJ_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {S : Finset I}
  {f : I → ConfigSpace V → ℝ}
-- given
  (hf : V → ℝ) :
-- imply
  expJ G.edgeFinset K hf (fun cfg => ∑ i ∈ S, f i cfg) = ∑ i ∈ S, expJ G.edgeFinset K hf (f i) := by
-- proof
  apply StatMech.Ising.ghsi_expJ_sum G K hf S f

/--
[ghsi_expJ_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_expJ_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {c : ℝ}
  {f : ConfigSpace V → ℝ}
-- given
  (hf : V → ℝ) :
-- imply
  expJ G.edgeFinset K hf (fun cfg => c * f cfg) = c * expJ G.edgeFinset K hf f := by
-- proof
  apply StatMech.Ising.ghsi_expJ_const_mul G K hf c f

/--
[ghsi_expJ_dirSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_expJ_dirSpin_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
-- given
  (hf dir : V → ℝ) :
-- imply
  expJ G.edgeFinset K hf (ghsiDirSpin dir) = ∑ x, dir x * expJ G.edgeFinset K hf (fun s => spin s x) := by
-- proof
  apply StatMech.Ising.ghsi_expJ_dirSpin G K hf dir

/--
[ghsi_expJ_mul_dirSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_expJ_mul_dirSpin_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {f : ConfigSpace V → ℝ}
-- given
  (hf dir : V → ℝ) :
-- imply
  expJ G.edgeFinset K hf (fun s => f s * ghsiDirSpin dir s) = ∑ x, dir x * expJ G.edgeFinset K hf (fun s => f s * spin s x) := by
-- proof
  apply StatMech.Ising.ghsi_expJ_mul_dirSpin G K hf dir f

/--
[ghsi_expJ_mul_dirSpin_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_expJ_mul_dirSpin_sq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {f : ConfigSpace V → ℝ}
-- given
  (hf dir : V → ℝ) :
-- imply
  expJ G.edgeFinset K hf (fun s => f s * ghsiDirSpin dir s * ghsiDirSpin dir s) = ∑ x, ∑ y, dir x * dir y * expJ G.edgeFinset K hf (fun s => f s * spin s x * spin s y) := by
-- proof
  apply StatMech.Ising.ghsi_expJ_mul_dirSpin_sq G K hf dir f

/--
[ghsi_directionalCovariance_eq_sum_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_directionalCovariance_eq_sum_covariance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {o : V}
-- given
  (hf dir : V → ℝ) :
-- imply
  ghsiDirectionalCovariance G K hf dir (fun s => spin s o) = ∑ x, dir x * ghsiCovariance G K hf o x := by
-- proof
  apply StatMech.Ising.ghsi_directionalCovariance_eq_sum_covariance G K hf dir o

/--
[ghsi_hasDerivAt_covariance_fieldLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_hasDerivAt_covariance_fieldLine_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {o x : V}
  {t : ℝ}
-- given
  (hf dir : V → ℝ) :
-- imply
  HasDerivAt (fun u => ghsiCovariance G K (ghsiFieldLine hf dir u) o x) (∑ y, dir y * ghsiUrsell3 G K (ghsiFieldLine hf dir t) o x y) t := by
-- proof
  apply StatMech.Ising.ghsi_hasDerivAt_covariance_fieldLine G K hf dir o x t

/--
[ghsi_hasDerivAt_directionalCovariance_ursellSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_hasDerivAt_directionalCovariance_ursellSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {o : V}
  {t : ℝ}
-- given
  (hf dir : V → ℝ) :
-- imply
  HasDerivAt (fun u => ghsiDirectionalCovariance G K (ghsiFieldLine hf dir u) dir (fun s => spin s o)) (∑ x, ∑ y, dir x * dir y * ghsiUrsell3 G K (ghsiFieldLine hf dir t) o x y) t := by
-- proof
  apply StatMech.Ising.ghsi_hasDerivAt_directionalCovariance_ursellSum G K hf dir o t

/--
[ghsi_directionalCovariance_derivValue_eq_ursellSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_directionalCovariance_derivValue_eq_ursellSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {o : V}
-- given
  (hf dir : V → ℝ) :
-- imply
  (expJ G.edgeFinset K hf (fun s => spin s o * ghsiDirSpin dir s * ghsiDirSpin dir s) - expJ G.edgeFinset K hf (fun s => spin s o * ghsiDirSpin dir s) * expJ G.edgeFinset K hf (ghsiDirSpin dir) - (expJ G.edgeFinset K hf (fun s => spin s o * ghsiDirSpin dir s) - expJ G.edgeFinset K hf (fun s => spin s o) * expJ G.edgeFinset K hf (ghsiDirSpin dir)) * expJ G.edgeFinset K hf (ghsiDirSpin dir) - expJ G.edgeFinset K hf (fun s => spin s o) * (expJ G.edgeFinset K hf (fun s => ghsiDirSpin dir s * ghsiDirSpin dir s) - expJ G.edgeFinset K hf (ghsiDirSpin dir) * expJ G.edgeFinset K hf (ghsiDirSpin dir))) = ∑ x, ∑ y, dir x * dir y * ghsiUrsell3 G K hf o x y := by
-- proof
  apply StatMech.Ising.ghsi_directionalCovariance_derivValue_eq_ursellSum G K hf dir o

/--
[ghsi_magnetization_fieldLine_concaveOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_magnetization_fieldLine_concaveOn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {o : V}
-- given
  (hf dir : V → ℝ)
  (hK : ∀ e, 0 ≤ K e)
  (hhf : ∀ x, 0 ≤ hf x)
  (hdir : ∀ x, 0 ≤ dir x)
  (hdiro : dir o = 0) :
-- imply
  ConcaveOn ℝ (Ici 0) (fun t => expJ G.edgeFinset K (ghsiFieldLine hf dir t) (fun s => spin s o)) := by
-- proof
  apply StatMech.Ising.ghsi_magnetization_fieldLine_concaveOn G K hf dir hK hhf hdir o hdiro

/--
[ghsi_directionalCovariance_le_secant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean)
-/
@[path]
private lemma ghsi_directionalCovariance_le_secant_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {o : V}
  {b : ℝ}
-- given
  (hf dir : V → ℝ)
  (hK : ∀ e, 0 ≤ K e)
  (hhf : ∀ x, 0 ≤ hf x)
  (hdir : ∀ x, 0 ≤ dir x)
  (hdiro : dir o = 0)
  (hb : 0 < b) :
-- imply
  ghsiDirectionalCovariance G K (ghsiFieldLine hf dir b) dir (fun s => spin s o) ≤ (expJ G.edgeFinset K (ghsiFieldLine hf dir b) (fun s => spin s o) - expJ G.edgeFinset K (ghsiFieldLine hf dir 0) (fun s => spin s o)) / b := by
-- proof
  apply StatMech.Ising.ghsi_directionalCovariance_le_secant G K hf dir hK hhf hdir o hdiro hb


-- created on 2026-10-23
