import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.GHSLebowitz
open Finset SimpleGraph Set StatMech StatMech.Ising


/--
[ghsL_ursell_eq_four_duplicate_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_ursell_eq_four_duplicate_cov_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => spin s o * (spin s x * spin s y)) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x * spin s y) - isingExpectation G β h (fun s => spin s o * spin s x) * isingExpectation G β h (fun s => spin s y) - isingExpectation G β h (fun s => spin s o * spin s y) * isingExpectation G β h (fun s => spin s x) + 2 * isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x) * isingExpectation G β h (fun s => spin s y) = 4 * (isingExp2 G β h (fun a b => uvar a b o * uvar a b x * tvar a b y) - isingExp2 G β h (fun a b => uvar a b o * uvar a b x) * isingExp2 G β h (fun a b => tvar a b y)) := by
-- proof
  apply StatMech.Ising.ghsL_ursell_eq_four_duplicate_cov G β h o x y

/--
[ghsL_pair_of_duplicate_cov_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_pair_of_duplicate_cov_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hcov : isingExp2 G β h (fun a b => uvar a b o * uvar a b x * tvar a b y) ≤ isingExp2 G β h (fun a b => uvar a b o * uvar a b x) * isingExp2 G β h (fun a b => tvar a b y)) :
-- imply
  cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) := by
-- proof
  apply StatMech.Ising.ghsL_pair_of_duplicate_cov_nonpos G β h o x y hcov

/--
[ghsLAgreement_mate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLAgreement_mate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V} :
-- imply
  ghsLAgreement (V := V) a (ghsLMate q a) = q := by
-- proof
  apply StatMech.Ising.ghsLAgreement_mate G q a

/--
[ghsLMate_agreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLMate_agreement_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace V} :
-- imply
  ghsLMate (ghsLAgreement (V := V) a b) a = b := by
-- proof
  apply StatMech.Ising.ghsLMate_agreement G a b

/--
[ghsL_uvar_mate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_uvar_mate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
  {v : V} :
-- imply
  uvar a (ghsLMate q a) v = if q v then 0 else spin a v := by
-- proof
  apply StatMech.Ising.ghsL_uvar_mate G q a v

/--
[ghsL_tvar_mate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_tvar_mate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
  {v : V} :
-- imply
  tvar a (ghsLMate q a) v = if q v then spin a v else 0 := by
-- proof
  apply StatMech.Ising.ghsL_tvar_mate G q a v

/--
[mem_ghsLAgreeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma mem_ghsLAgreeFinset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ConfigSpace V}
  {v : V} :
-- imply
  v ∈ ghsLAgreeFinset q ↔ q v = true := by
-- proof
  apply StatMech.Ising.mem_ghsLAgreeFinset G q v

/--
[ghsLAgreeFinset_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLAgreeFinset_monotone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Monotone (ghsLAgreeFinset : ConfigSpace V → Finset V) := by
-- proof
  apply StatMech.Ising.ghsLAgreeFinset_monotone G

/--
[ghsLAgreeFinset_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLAgreeFinset_sup_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q r : ConfigSpace V} :
-- imply
  ghsLAgreeFinset (q ⊔ r) = ghsLAgreeFinset q ∪ ghsLAgreeFinset r := by
-- proof
  apply StatMech.Ising.ghsLAgreeFinset_sup G q r

/--
[ghsLAgreeFinset_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLAgreeFinset_inf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q r : ConfigSpace V} :
-- imply
  ghsLAgreeFinset (q ⊓ r) = ghsLAgreeFinset q ∩ ghsLAgreeFinset r := by
-- proof
  apply StatMech.Ising.ghsLAgreeFinset_inf G q r

/--
[ghsL_bond_add_mate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_bond_add_mate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  bond a e + bond (ghsLMate q a) e = if Sharpness.edgeInside (ghsLAgreeFinset q) e then 2 * bond a e else if Sharpness.edgeInside (ghsLAgreeFinset q)ᶜ e then 2 * bond a e else 0 := by
-- proof
  apply StatMech.Ising.ghsL_bond_add_mate G q a e

/--
[ghsL_spin_add_mate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_spin_add_mate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
  {v : V} :
-- imply
  spin a v + spin (ghsLMate q a) v = if q v then 2 * spin a v else 0 := by
-- proof
  apply StatMech.Ising.ghsL_spin_add_mate G q a v

/--
[ghsL_bondSum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_bondSum_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V} :
-- imply
  (∑ e ∈ G.edgeFinset, bond a e) + ∑ e ∈ G.edgeFinset, bond (ghsLMate q a) e = 2 * (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q), bond a e) + 2 * (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ, bond a e) := by
-- proof
  apply StatMech.Ising.ghsL_bondSum_split G q a

/--
[ghsL_spinSum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_spinSum_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V} :
-- imply
  (∑ v : V, spin a v) + ∑ v : V, spin (ghsLMate q a) v = 2 * ∑ v ∈ ghsLAgreeFinset q, spin a v := by
-- proof
  apply StatMech.Ising.ghsL_spinSum_split G q a

/--
[ghsL_duplicateWeight_eq_tWeight_mul_uWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_duplicateWeight_eq_tWeight_mul_uWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  isingWeight G β h a * isingWeight G β h (ghsLMate q a) = ghsLTWeight G β h q a * ghsLUWeight G β q a := by
-- proof
  apply StatMech.Ising.ghsL_duplicateWeight_eq_tWeight_mul_uWeight G β h q a

/--
[ghsL_split_sum_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_split_sum_product_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ConfigSpace V}
-- given
  (f : ((v : {v : V // q v = true}) → Bool) → ℝ)
  (g : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ) :
-- imply
  (∑ a : ConfigSpace V, f (ghsLSplitEquiv q a).1 * g (ghsLSplitEquiv q a).2) = (∑ st, f st) * ∑ su, g su := by
-- proof
  apply StatMech.Ising.ghsL_split_sum_product G q f g

/--
[ghsL_split_cross_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_split_cross_product_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ConfigSpace V}
-- given
  (f₀ f₁ : ((v : {v : V // q v = true}) → Bool) → ℝ)
  (g₀ g₁ : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ) :
-- imply
  (∑ a : ConfigSpace V, f₀ (ghsLSplitEquiv q a).1 * g₀ (ghsLSplitEquiv q a).2) * (∑ a : ConfigSpace V, f₁ (ghsLSplitEquiv q a).1 * g₁ (ghsLSplitEquiv q a).2) = (∑ a : ConfigSpace V, f₀ (ghsLSplitEquiv q a).1 * g₁ (ghsLSplitEquiv q a).2) * (∑ a : ConfigSpace V, f₁ (ghsLSplitEquiv q a).1 * g₀ (ghsLSplitEquiv q a).2) := by
-- proof
  apply StatMech.Ising.ghsL_split_cross_product G q f₀ f₁ g₀ g₁

/--
[ghsLTComplete_eq_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLTComplete_eq_on_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
  {v : V}
-- given
  (hv : q v = true) :
-- imply
  ghsLTComplete q (ghsLSplitEquiv q a).1 v = a v := by
-- proof
  apply StatMech.Ising.ghsLTComplete_eq_on G q a hv

/--
[ghsLUComplete_eq_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLUComplete_eq_on_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
  {v : V}
-- given
  (hv : ¬ q v = true) :
-- imply
  ghsLUComplete q (ghsLSplitEquiv q a).2 v = a v := by
-- proof
  apply StatMech.Ising.ghsLUComplete_eq_on G q a hv

/--
[ghsLTWeight_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLTWeight_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  ghsLTWeight G β h q a = ghsLTWeight G β h q (ghsLTComplete q (ghsLSplitEquiv q a).1) := by
-- proof
  apply StatMech.Ising.ghsLTWeight_split G β h q a

/--
[ghsLUWeight_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLUWeight_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {q a : ConfigSpace V} :
-- imply
  ghsLUWeight G β q a = ghsLUWeight G β q (ghsLUComplete q (ghsLSplitEquiv q a).2) := by
-- proof
  apply StatMech.Ising.ghsLUWeight_split G β q a

/--
[ghsL_tvar_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_tvar_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
  {y : V} :
-- imply
  tvar a (ghsLMate q a) y = tvar (ghsLTComplete q (ghsLSplitEquiv q a).1) (ghsLMate q (ghsLTComplete q (ghsLSplitEquiv q a).1)) y := by
-- proof
  apply StatMech.Ising.ghsL_tvar_split G q a y

/--
[ghsL_uvar_mul_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_uvar_mul_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
  {o x : V} :
-- imply
  uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x = uvar (ghsLUComplete q (ghsLSplitEquiv q a).2) (ghsLMate q (ghsLUComplete q (ghsLSplitEquiv q a).2)) o * uvar (ghsLUComplete q (ghsLSplitEquiv q a).2) (ghsLMate q (ghsLUComplete q (ghsLSplitEquiv q a).2)) x := by
-- proof
  apply StatMech.Ising.ghsL_uvar_mul_split G q a o x

/--
[ghsL_sum_pair_xnor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_sum_pair_xnor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : ConfigSpace V → ConfigSpace V → ℝ} :
-- imply
  (∑ a : ConfigSpace V, ∑ b : ConfigSpace V, F a b) = ∑ q : ConfigSpace V, ∑ a : ConfigSpace V, F a (ghsLMate q a) := by
-- proof
  apply StatMech.Ising.ghsL_sum_pair_xnor G F

/--
[ghsLFibreWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLFibreWeight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  0 < ghsLFibreWeight G β h q a := by
-- proof
  apply StatMech.Ising.ghsLFibreWeight_pos G β h q a

/--
[ghsLFibreMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLFibreMass_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  0 < ghsLFibreMass G β h q := by
-- proof
  apply StatMech.Ising.ghsLFibreMass_pos G β h q

/--
[ghsLAgreementProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLAgreementProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  0 ≤ ghsLAgreementProb G β h := by
-- proof
  apply StatMech.Ising.ghsLAgreementProb_nonneg G β h

/--
[ghsLAgreementProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLAgreementProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  ∑ q : ConfigSpace V, ghsLAgreementProb G β h q = 1 := by
-- proof
  apply StatMech.Ising.ghsLAgreementProb_sum_eq_one G β h

/--
[ghsLAgreementProb_fkg_of_subsetMass_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLAgreementProb_fkg_of_subsetMass_scale_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h c : ℝ)
  (hc : 0 < c)
  (hscale : ∀ q : ConfigSpace V, ghsvp_subsetMass G β h (ghsLAgreeFinset q) = c * ghsLFibreMass G β h q)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  FKGLatticeCondition (ghsLAgreementProb G β h) := by
-- proof
  apply StatMech.Ising.ghsLAgreementProb_fkg_of_subsetMass_scale G β h c hc hscale hβ hh

/--
[ghsLTWeight_eq_wJ_restricted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLTWeight_eq_wJ_restricted_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  ghsLTWeight G β h q a = Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)) (fun _ => 2 * β) (fun x => if x ∈ ghsLAgreeFinset q then 2 * β * h else 0) a := by
-- proof
  apply StatMech.Ising.ghsLTWeight_eq_wJ_restricted G β h q a

/--
[ghsLUWeight_eq_wJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLUWeight_eq_wJ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {q a : ConfigSpace V} :
-- imply
  ghsLUWeight G β q a = Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ) (fun _ => 2 * β) (fun _ => 0) a := by
-- proof
  apply StatMech.Ising.ghsLUWeight_eq_wJ G β q a

/--
[ghsvp_subsetMass_eq_card_mul_fibreMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsvp_subsetMass_eq_card_mul_fibreMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  ghsvp_subsetMass G β h (ghsLAgreeFinset q) = (4 * Fintype.card (ConfigSpace V)) * ghsLFibreMass G β h q := by
-- proof
  apply StatMech.Ising.ghsvp_subsetMass_eq_card_mul_fibreMass G β h q

/--
[ghsL_isIngExp2_fibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_isIngExp2_fibre_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : ConfigSpace V → ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp2 G β h F = ∑ q : ConfigSpace V, ghsLAgreementProb G β h q * ghsLFibreExpectation G β h F q := by
-- proof
  apply StatMech.Ising.ghsL_isIngExp2_fibre G β h F

/--
[ghsLFibreExpectation_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLFibreExpectation_const_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ConfigSpace V}
-- given
  (β h r : ℝ) :
-- imply
  ghsLFibreExpectation G β h (fun _ _ => r) q = r := by
-- proof
  apply StatMech.Ising.ghsLFibreExpectation_const G β h r q

/--
[ghsL_fkg_antitone_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_fkg_antitone_monotone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {π : ConfigSpace V → ℝ}
  {f g : ConfigSpace V → ℝ}
-- given
  (hπ₀ : 0 ≤ π)
  (hnorm : ∑ q, π q = 1)
  (hπ : FKGLatticeCondition π)
  (hf : Antitone f)
  (hg : Monotone g) :
-- imply
  (∑ q, π q * (f q * g q)) ≤ (∑ q, π q * f q) * (∑ q, π q * g q) := by
-- proof
  apply StatMech.Ising.ghsL_fkg_antitone_monotone G hπ₀ hnorm hπ hf hg

/--
[ghsLUWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLUWeight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {q a : ConfigSpace V} :
-- imply
  0 < ghsLUWeight G β q a := by
-- proof
  apply StatMech.Ising.ghsLUWeight_pos G β q a

/--
[ghsLTWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLTWeight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  0 < ghsLTWeight G β h q a := by
-- proof
  apply StatMech.Ising.ghsLTWeight_pos G β h q a

/--
[ghsLFibreUU_eq_uExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLFibreUU_eq_uExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
  {q : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  ghsLFibreUU G β h o x q = ghsLUExpectation G β q (fun a => uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x) := by
-- proof
  apply StatMech.Ising.ghsLFibreUU_eq_uExpectation G β h o x q

/--
[ghsLFibreUU_eq_disagreementCorr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLFibreUU_eq_disagreementCorr_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
  {q : ConfigSpace V}
-- given
  (β h : ℝ)
  (hox : o ≠ x) :
-- imply
  ghsLFibreUU G β h o x q = ghsvp_disagreementCorr G β o x (ghsLAgreeFinset q) := by
-- proof
  apply StatMech.Ising.ghsLFibreUU_eq_disagreementCorr G β h o x hox q

/--
[ghsLFibreT_eq_tExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLFibreT_eq_tExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {y : V}
  {q : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  ghsLFibreT G β h y q = ghsLTExpectation G β h q (fun a => tvar a (ghsLMate q a) y) := by
-- proof
  apply StatMech.Ising.ghsLFibreT_eq_tExpectation G β h y q

/--
[ghsLOutFieldWeight_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLOutFieldWeight_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  ghsLOutFieldWeight β h q a = ghsLOutFieldWeight β h q (ghsLUComplete q (ghsLSplitEquiv q a).2) := by
-- proof
  apply StatMech.Ising.ghsLOutFieldWeight_split G β h q a

/--
[ghsL_wJ_field_eq_tWeight_mul_out](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_wJ_field_eq_tWeight_mul_out_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q a : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)) (fun _ => 2 * β) (fun _ => 2 * β * h) a = ghsLTWeight G β h q a * ghsLOutFieldWeight β h q a := by
-- proof
  apply StatMech.Ising.ghsL_wJ_field_eq_tWeight_mul_out G β h q a

/--
[ghsLFibreT_eq_agreementMag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLFibreT_eq_agreementMag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {y : V}
  {q : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  ghsLFibreT G β h y q = ghsvp_agreementMag G β h y (ghsLAgreeFinset q) := by
-- proof
  apply StatMech.Ising.ghsLFibreT_eq_agreementMag G β h y q

/--
[ghsL_fibreFactorization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_fibreFactorization_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  GHSLebowitzFibreFactorization G β h o x y := by
-- proof
  apply StatMech.Ising.ghsL_fibreFactorization G β h o x y

/--
[ghsL_duplicate_cov_nonpos_of_fibres](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_duplicate_cov_nonpos_of_fibres_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hlattice : FKGLatticeCondition (ghsLAgreementProb G β h))
  (hfactor : GHSLebowitzFibreFactorization G β h o x y)
  (huu : Antitone (ghsLFibreUU G β h o x))
  (ht : Monotone (ghsLFibreT G β h y)) :
-- imply
  isingExp2 G β h (fun a b => uvar a b o * uvar a b x * tvar a b y) ≤ isingExp2 G β h (fun a b => uvar a b o * uvar a b x) * isingExp2 G β h (fun a b => tvar a b y) := by
-- proof
  apply StatMech.Ising.ghsL_duplicate_cov_nonpos_of_fibres G β h o x y hlattice hfactor huu ht

/--
[ghsLFibreUU_antitone_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLFibreUU_antitone_of_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hdict : ∀ q : ConfigSpace V, ghsLFibreUU G β h o x q = ghsvp_disagreementCorr G β o x (ghsLAgreeFinset q)) :
-- imply
  Antitone (ghsLFibreUU G β h o x) := by
-- proof
  apply StatMech.Ising.ghsLFibreUU_antitone_of_eq G β h hβ o x hdict

/--
[ghsLFibreT_monotone_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLFibreT_monotone_of_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hdict : ∀ q : ConfigSpace V, ghsLFibreT G β h y q = ghsvp_agreementMag G β h y (ghsLAgreeFinset q)) :
-- imply
  Monotone (ghsLFibreT G β h y) := by
-- proof
  apply StatMech.Ising.ghsLFibreT_monotone_of_eq G β h hβ hh y hdict

/--
[ghsL_pair_of_vertexPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_pair_of_vertexPartition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h c : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hc : 0 < c)
  (hmass : ∀ q : ConfigSpace V, ghsvp_subsetMass G β h (ghsLAgreeFinset q) = c * ghsLFibreMass G β h q)
  (huu : ∀ q : ConfigSpace V, ghsLFibreUU G β h o x q = ghsvp_disagreementCorr G β o x (ghsLAgreeFinset q))
  (ht : ∀ q : ConfigSpace V, ghsLFibreT G β h y q = ghsvp_agreementMag G β h y (ghsLAgreeFinset q)) :
-- imply
  cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) := by
-- proof
  apply StatMech.Ising.ghsL_pair_of_vertexPartition G β h c hβ hh hc o x y hmass huu ht

/--
[ghsLAgreementProb_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsLAgreementProb_fkg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  FKGLatticeCondition (ghsLAgreementProb G β h) := by
-- proof
  apply StatMech.Ising.ghsLAgreementProb_fkg G β h hβ hh

/--
[ghsL_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_pair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x) :
-- imply
  cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) := by
-- proof
  apply StatMech.Ising.ghsL_pair G β h hβ hh o x y hox

/--
[ghsL_threePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_threePoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Ising.ghsL_threePoint G β h hβ hh o

/--
[ghsL_pair_of_fibres](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_pair_of_fibres_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hlattice : FKGLatticeCondition (ghsLAgreementProb G β h))
  (hfactor : GHSLebowitzFibreFactorization G β h o x y)
  (huu : Antitone (ghsLFibreUU G β h o x))
  (ht : Monotone (ghsLFibreT G β h y)) :
-- imply
  cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) := by
-- proof
  apply StatMech.Ising.ghsL_pair_of_fibres G β h o x y hlattice hfactor huu ht

/--
[ghsL_threePoint_of_fibres](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean)
-/
@[path]
private lemma ghsL_threePoint_of_fibres_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hlattice : FKGLatticeCondition (ghsLAgreementProb G β h))
  (hfactor : ∀ x y, GHSLebowitzFibreFactorization G β h o x y)
  (huu : ∀ x, Antitone (ghsLFibreUU G β h o x))
  (ht : ∀ y, Monotone (ghsLFibreT G β h y)) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Ising.ghsL_threePoint_of_fibres G β h o hlattice hfactor huu ht


-- created on 2026-10-23
