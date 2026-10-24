import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass
open Finset SimpleGraph StatMech StatMech.Sharpness


/--
[sum_cutMassNumerator_eq_sourcePairDisconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma sum_cutMassNumerator_eq_sourcePairDisconn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {o g : V} :
-- imply
  (∑ S : Finset V, if o ∈ S then gatedSourcePairSum G beta J ∅ ∅ (fun m => notConnComp G m g = S) else 0) = sourcePairDisconnSum G beta J ∅ ∅ o g := by
-- proof
  apply StatMech.Sharpness.sum_cutMassNumerator_eq_sourcePairDisconn G beta J o g

/--
[sum_isingCutMass_eq_one_sub_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma sum_isingCutMass_eq_one_sub_sq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {o g : V}
-- given
  (hog : o ≠ g) :
-- imply
  (∑ S : Finset V, if o ∈ S then isingCutMass G beta J g S else 0) = 1 - (expectationJ G beta J {o, g}) ^ 2 := by
-- proof
  apply StatMech.Sharpness.sum_isingCutMass_eq_one_sub_sq G beta J hog

/--
[isingCutMass_eq_zero_of_mem_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma isingCutMass_eq_zero_of_mem_root_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {g : V}
  {S : Finset V}
-- given
  (hg : g ∈ S) :
-- imply
  isingCutMass G beta J g S = 0 := by
-- proof
  apply StatMech.Sharpness.isingCutMass_eq_zero_of_mem_root G beta J g S hg

/--
[isingCutMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma isingCutMass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {g : V}
  {S : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ isingCutMass G beta J g S := by
-- proof
  apply StatMech.Sharpness.isingCutMass_nonneg G beta J hbeta hJ g S

/--
[sum_localCorr_mul_cutMassNumerator_eq_sourcePairDisconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma sum_localCorr_mul_cutMassNumerator_eq_sourcePairDisconn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {o x g : V}
-- given
  (hox : o ≠ x) :
-- imply
  (∑ S : Finset V, if o ∈ S ∧ x ∈ S ∧ g ∉ S then expectationJ G beta (couplingIn J S) {o, x} * gatedSourcePairSum G beta J ∅ ∅ (fun m => notConnComp G m g = S) else 0) = sourcePairDisconnSum G beta J {o, x} ∅ o g := by
-- proof
  apply StatMech.Sharpness.sum_localCorr_mul_cutMassNumerator_eq_sourcePairDisconn G beta J hox

/--
[sum_localCorr_mul_isingCutMass_eq_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma sum_localCorr_mul_isingCutMass_eq_covariance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {o x g : V}
-- given
  (hox : o ≠ x)
  (hog : o ≠ g)
  (hxg : x ≠ g) :
-- imply
  (∑ S : Finset V, if o ∈ S ∧ x ∈ S ∧ g ∉ S then expectationJ G beta (couplingIn J S) {o, x} * isingCutMass G beta J g S else 0) = expectationJ G beta J {o, x} - expectationJ G beta J {o, g} * expectationJ G beta J {x, g} := by
-- proof
  apply StatMech.Sharpness.sum_localCorr_mul_isingCutMass_eq_covariance G beta J hox hog hxg

/--
[sum_localCorr_mul_fieldGhostCutMass_eq_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma sum_localCorr_mul_fieldGhostCutMass_eq_covariance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
-- given
  (beta h : ℝ)
  (hox : o ≠ x) :
-- imply
  (∑ S : Finset (Option V), if some o ∈ S ∧ some x ∈ S ∧ none ∉ S then expectationJ (withGhost G) beta (couplingIn (ghostCoupling h beta (fun _ => 1)) S) {some o, some x} * isingCutMass (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) none S else 0) = Ising.isingExpectation G beta h (Ising.spinProd {o, x}) - Ising.isingExpectation G beta h (Ising.spinProd {o}) * Ising.isingExpectation G beta h (Ising.spinProd {x}) := by
-- proof
  apply StatMech.Sharpness.sum_localCorr_mul_fieldGhostCutMass_eq_covariance G beta h hox

/--
[weightedExpectation_zero_eq_expectationJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma weightedExpectation_zero_eq_expectationJ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  WeightedFieldGhost.weightedExpectation G beta J 0 (Ising.spinProd A) = expectationJ G beta J A := by
-- proof
  apply StatMech.Sharpness.weightedExpectation_zero_eq_expectationJ G beta J A

/--
[couplingIn_ghostCoupling_map_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma couplingIn_ghostCoupling_map_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {T : Finset V}
-- given
  (beta h : ℝ) :
-- imply
  couplingIn (ghostCoupling h beta (fun _ => 1)) (T.map someEmb) = ghostCoupling 0 beta (couplingIn (fun _ => 1) T) := by
-- proof
  apply StatMech.Sharpness.couplingIn_ghostCoupling_map_some G beta h T

/--
[localCorr_fieldGhost_map_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma localCorr_fieldGhost_map_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {T : Finset V}
  {o x : V}
-- given
  (beta h : ℝ)
  (hox : o ≠ x) :
-- imply
  expectationJ (withGhost G) beta (couplingIn (ghostCoupling h beta (fun _ => 1)) (T.map someEmb)) {some o, some x} = expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} := by
-- proof
  apply StatMech.Sharpness.localCorr_fieldGhost_map_some G beta h T hox

/--
[sum_baseCutMass_eq_one_sub_mag_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma sum_baseCutMass_eq_one_sub_mag_sq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (beta h : ℝ) :
-- imply
  (∑ T : Finset V, if o ∈ T then isingCutMass (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb) else 0) = 1 - (Ising.isingExpectation G beta h (Ising.spinProd {o})) ^ 2 := by
-- proof
  apply StatMech.Sharpness.sum_baseCutMass_eq_one_sub_mag_sq G beta h o

/--
[sum_localCorr_baseCutMass_eq_fieldCovariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma sum_localCorr_baseCutMass_eq_fieldCovariance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
-- given
  (beta h : ℝ)
  (hox : o ≠ x) :
-- imply
  (∑ T : Finset V, if o ∈ T ∧ x ∈ T then expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} * isingCutMass (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb) else 0) = Ising.isingExpectation G beta h (Ising.spinProd {o, x}) - Ising.isingExpectation G beta h (Ising.spinProd {o}) * Ising.isingExpectation G beta h (Ising.spinProd {x}) := by
-- proof
  apply StatMech.Sharpness.sum_localCorr_baseCutMass_eq_fieldCovariance G beta h hox

/--
[normalizedDeltaLowerMass_fieldGhost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma normalizedDeltaLowerMass_fieldGhost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (beta h : ℝ)
  (hox : o ≠ x) :
-- imply
  (currentSum (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 * isingDeltaLowerMass (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) (some o) (some x) (some y) none = ∑ T : Finset V, if o ∈ T ∧ x ∈ T ∧ y ∉ T then expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} * isingCutMass (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb) else 0 := by
-- proof
  apply StatMech.Sharpness.normalizedDeltaLowerMass_fieldGhost G beta h hox

/--
[normalizedDeltaSelfLowerMass_fieldGhost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma normalizedDeltaSelfLowerMass_fieldGhost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o y : V}
-- given
  (beta h : ℝ) :
-- imply
  (currentSum (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 * isingDeltaSelfLowerMass (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) (some o) (some y) none = ∑ T : Finset V, if o ∈ T ∧ y ∉ T then isingCutMass (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb) else 0 := by
-- proof
  apply StatMech.Sharpness.normalizedDeltaSelfLowerMass_fieldGhost G beta h o y

/--
[localizedGraph_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma localizedGraph_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {T : Finset V}
  [DecidableRel (localizedGraph G T).Adj] :
-- imply
  (localizedGraph G T).edgeFinset = edgesIn G T := by
-- proof
  apply StatMech.Sharpness.localizedGraph_edgeFinset G T

/--
[expectationJ_couplingIn_one_eq_induced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma expectationJ_couplingIn_one_eq_induced_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {T : Finset V}
  {o x : V}
-- given
  (ho : o ∈ T)
  (hx : x ∈ T) :
-- imply
  expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} = Ising.isingExpectation (G.comap (Subtype.val : {v // v ∈ T} → V)) beta 0 (Ising.spinProd {⟨o, ho⟩, ⟨x, hx⟩}) := by
-- proof
  apply StatMech.Sharpness.expectationJ_couplingIn_one_eq_induced G beta T ho hx

/--
[hcaBondDelta_incident_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma hcaBondDelta_incident_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o y : V}
-- given
  (beta h : ℝ)
  (hoy : o ≠ y) :
-- imply
  HcovAssembly.hcaBondDelta G beta h o s(o, y) = sourcePairDisconnSum (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) {some y, none} ∅ (some o) none := by
-- proof
  apply StatMech.Sharpness.hcaBondDelta_incident_eq G beta h o y hoy

/--
[hcaBondDelta_incident_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma hcaBondDelta_incident_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o y : V}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hoy : o ≠ y) :
-- imply
  Ising.isingExpectation G beta h (Ising.spinProd {y}) * HcovAssembly.hcaBondDelta G beta h o s(o, y) ≥ isingDeltaSelfLowerMass (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) (some o) (some y) none := by
-- proof
  apply StatMech.Sharpness.hcaBondDelta_incident_bound G beta h hbeta hh o y hoy

/--
[hcaBondDelta_nonincident_eq_deltaPair_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma hcaBondDelta_nonincident_eq_deltaPair_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (beta h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  HcovAssembly.hcaBondDelta G beta h o s(x, y) = isingDeltaPairSum (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) (some o) (some x) (some y) none + isingDeltaPairSum (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) (some o) (some y) (some x) none := by
-- proof
  apply StatMech.Sharpness.hcaBondDelta_nonincident_eq_deltaPair_add G beta h hox hoy hxy

/--
[isingDeltaPair_field_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean)
-/
@[path]
private lemma isingDeltaPair_field_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  Ising.isingExpectation G beta h (Ising.spinProd {y}) * isingDeltaPairSum (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) (some o) (some x) (some y) none ≥ isingDeltaLowerMass (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) (some o) (some x) (some y) none := by
-- proof
  apply StatMech.Sharpness.isingDeltaPair_field_bound G beta h hbeta hh hox hoy hxy


-- created on 2026-10-23
