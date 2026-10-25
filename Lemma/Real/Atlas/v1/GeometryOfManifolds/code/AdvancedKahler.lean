import Mathlib
import sympy.Basic
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
open DifferentialFormSpace


/--
[hodge_conjugation_symmetry](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma hodge_conjugation_symmetry
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  [hH : @HasHodgeNumbers Ω VF inst]
  {p q : ℕ}
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler S J) :
-- imply
  hH.hodge p q = hH.hodge q p :=
-- proof
  hH.conjugation_symmetry p q

/--
[betti_eq_sum_hodge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma betti_eq_sum_hodge
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  [hH : @HasHodgeNumbers Ω VF inst]
  {k : ℕ}
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler S J) :
-- imply
  hH.betti k = (Finset.range (k + 1)).sum (fun p => hH.hodge p (k - p)) :=
-- proof
  hH.betti_hodge_link k

/--
[compact_kahler_odd_betti_even](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma compact_kahler_odd_betti_even
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {k : ℕ}
  [hH : @HasHodgeNumbers Ω VF inst]
-- given
  (J : AlmostComplexStr (inst := inst))
  (hK : IsKahler S J)
  (hk : k % 2 = 1) :
-- imply
  ∃ (m : ℕ), hH.betti k = 2 * m := by
-- proof
  rw [betti_eq_sum_hodge S J hK k]
  set f := (fun p => hH.hodge p (k - p))
  have hf : ∀ p, p ≤ k → f p = f (k - p) := by
    intro p hp
    simp only [f]
    have h1 : k - (k - p) = p := Nat.sub_sub_self hp
    rw [hodge_conjugation_symmetry S J hK p (k - p)]
    congr 1; omega
  have ⟨j, hj⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
  subst hj
  have hlen : 2 * j + 1 + 1 = (j + 1) + (j + 1) := by omega
  rw [hlen, Finset.sum_range_add]
  suffices h : (Finset.range (j + 1)).sum (fun x => f (j + 1 + x)) =
    (Finset.range (j + 1)).sum f by
    rw [h]; exact ⟨_, (two_mul _).symm⟩
  apply Finset.sum_bij' (fun a _ => j - a) (fun a _ => j - a)
  · intro a ha
    simp only [Finset.mem_range] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    have hp : j + 1 + a ≤ 2 * j + 1 := by omega
    rw [hf (j + 1 + a) hp]
    congr 1
    omega

/--
[sqrt_div_eq_div_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma sqrt_div_eq_div_sqrt
  {C : ℝ}
  {k : ℕ}
-- given
  (hC : 0 < C)
  (_hk : k ≠ 0) :
-- imply
  Real.sqrt (C / (k : ℝ)) = Real.sqrt C / Real.sqrt (k : ℝ) := by
-- proof
  rw [Real.sqrt_div (le_of_lt hC)]

/--
[nat_rpow_one_third_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma nat_rpow_one_third_le
  {k : ℕ}
-- given
  (hk : 1 ≤ k) :
-- imply
  (k : ℝ) ^ ((1:ℝ)/3) ≤ (k : ℝ) := by
-- proof
  calc (k : ℝ) ^ ((1:ℝ)/3) ≤ (k : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hk) (by linarith)
    _ = k := by simp [Real.rpow_one]

/--
[exp_neg_linear_le_exp_neg_cuberoot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma exp_neg_linear_le_exp_neg_cuberoot
  {lam : ℝ}
  {k : ℕ}
-- given
  (hlam : 0 < lam) :
-- imply
  Real.exp (-lam * (k : ℝ) / 3) ≤ Real.exp (-(lam / 3) * (k : ℝ) ^ ((1:ℝ)/3)) := by
-- proof
  apply Real.exp_le_exp.mpr
  obtain rfl | hk := Nat.eq_zero_or_pos k
  · simp
  · have hcr := nat_rpow_one_third_le k hk
    nlinarith [mul_le_mul_of_nonneg_left hcr (le_of_lt (div_pos hlam (by linarith : (0:ℝ) < 3)))]

/--
[IsExponentiallyClose.to_cube_root](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma IsExponentiallyClose.to_cube_root
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {wdn : WeightedDerivSupNorm Ω (inst := inst)}
  {fam fam' : ApproxHolomorphicSectionFamily (inst := inst)}
-- given
  (h : IsExponentiallyClose wdn fam fam') :
-- imply
  IsExponentiallyCloseCubeRoot wdn fam fam' where same_bundle :=
-- proof
  h.same_bundle
    exp_close_all_derivs := by
      obtain ⟨lam, hlam_pos, h_all⟩ := h.exp_close_all_derivs
      refine ⟨lam / 3, div_pos hlam_pos (by linarith : (0:ℝ) < 3), ?_⟩
      intro r
      obtain ⟨C_r, hC_pos, h_bound⟩ := h_all r
      refine ⟨C_r, hC_pos, ?_⟩
      intro k p
      calc wdn.weighted_supnorm k r (fam.section_ k p - fam'.section_ k p)
        ≤ C_r * Real.exp (-lam * (k : ℝ) / 3) := h_bound k p
        _ ≤ C_r * Real.exp (-(lam / 3) * (k : ℝ) ^ ((1:ℝ)/3)) := by
          apply mul_le_mul_of_nonneg_left
          · exact exp_neg_linear_le_exp_neg_cuberoot lam hlam_pos k
          · exact le_of_lt hC_pos

/--
[spectral_gap_from_curvature_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma spectral_gap_from_curvature_bound
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {greenCorrection : ℕ → Ω 0 → Ω 0}
  {C_geom : ℝ}
-- given
  (l2 : L2NormSpace Ω (inst := inst))
  (dol : DolbeaultOps (inst := inst))
  (hC_pos : C_geom > 0)
  (hcurv_bound : ∀ (k : ℕ) (s : Ω 0), (k : ℝ) > C_geom → l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤ 1 / ((k : ℝ) - C_geom) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s)))
  (hgeneral_bound : ∀ (k : ℕ), k ≠ 0 → ∀ (s : Ω 0), ∃ (B : ℝ), B > 0 ∧ l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤ B * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))) :
-- imply
  ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0), ∃ (c : ℝ), c > 0 ∧ l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤ c / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s)) := by
-- proof
  intro k hk s
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  by_cases hkC : (k : ℝ) > C_geom
  ·
    have hbound := hcurv_bound k s hkC
    have hkC_pos : (k : ℝ) - C_geom > 0 := by linarith
    refine ⟨(k : ℝ) / ((k : ℝ) - C_geom), ?_, ?_⟩
    ·
      exact div_pos hk_pos hkC_pos
    ·
      have h_eq : 1 / ((k : ℝ) - C_geom) = ((k : ℝ) / ((k : ℝ) - C_geom)) / (k : ℝ) := by
        field_simp
      rwa [h_eq] at hbound
  ·
    push_neg at hkC
    obtain ⟨B, hB_pos, hB_bound⟩ := hgeneral_bound k hk s
    refine ⟨B * (k : ℝ), ?_, ?_⟩
    ·
      exact mul_pos hB_pos hk_pos
    ·
      have h_eq : B * (k : ℝ) / (k : ℝ) = B := by
        field_simp
      rwa [h_eq]

/--
[green_corrected_family_is_holomorphic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma green_corrected_family_is_holomorphic
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  {gci : GreenCorrectionInput wdn l2 dol fam}
-- given
  (wdn : WeightedDerivSupNorm Ω (inst := inst))
  (l2 : L2NormSpace Ω (inst := inst))
  (dol : DolbeaultOps (inst := inst))
  (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
-- imply
  IsHolomorphicFamily dol (correctedFamily wdn l2 dol fam gci) := by
-- proof
  constructor
  intro k p
  simp only [correctedFamily]
  by_cases hk : k = 0
  ·
    subst hk
    exact gci.hol_at_zero p
  ·
    exact gci.greenOp.green_holomorphic k hk (fam.section_ k p)

/--
[green_correction_exp_close](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma green_correction_exp_close
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  {gci : GreenCorrectionInput wdn l2 dol fam}
-- given
  (wdn : WeightedDerivSupNorm Ω (inst := inst))
  (l2 : L2NormSpace Ω (inst := inst))
  (dol : DolbeaultOps (inst := inst))
  (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
-- imply
  IsExponentiallyCloseCubeRoot wdn fam (correctedFamily wdn l2 dol fam gci) := by
-- proof
  constructor
  ·
    exact gci.corrected_bundle_eq
  ·
    obtain ⟨C_l2, lam_l2, hCl2_pos, hlam_l2_pos, h_l2_bound⟩ := gci.correction_l2_exp_bound
    refine ⟨lam_l2, hlam_l2_pos, ?_⟩
    intro r
    obtain ⟨C_r, hCr_pos, h_cauchy⟩ := gci.cauchy_estimates r
    refine ⟨C_r * C_l2, mul_pos hCr_pos hCl2_pos, ?_⟩
    intro k p
    have h_diff : fam.section_ k p - (correctedFamily wdn l2 dol fam gci).section_ k p =
      -(gci.greenOp.greenCorrection k (fam.section_ k p)) := by
      simp only [correctedFamily]
      abel
    rw [h_diff]
    have h_neg := wdn.weighted_supnorm_neg k r (gci.greenOp.greenCorrection k (fam.section_ k p))
    have h_cauchy_k := h_cauchy k (fam.section_ k p)
    have h_l2_k := h_l2_bound k p
    calc wdn.weighted_supnorm k r (-(gci.greenOp.greenCorrection k (fam.section_ k p)))
      ≤ wdn.weighted_supnorm k r (gci.greenOp.greenCorrection k (fam.section_ k p)) := h_neg
      _ ≤ C_r * l2.l2norm (gci.greenOp.greenCorrection k (fam.section_ k p)) := h_cauchy_k
      _ ≤ C_r * (C_l2 * Real.exp (-lam_l2 * (k : ℝ) ^ ((1 : ℝ) / 3))) := by
        apply mul_le_mul_of_nonneg_left h_l2_k (le_of_lt hCr_pos)
      _ = C_r * C_l2 * Real.exp (-lam_l2 * (k : ℝ) ^ ((1 : ℝ) / 3)) := by ring

/--
[gaussian_peak_sections_exist_sorry](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma gaussian_peak_sections_exist_sorry
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  {S : SymplecticManifold Ω VF}
  [HasGaussianPeakData Ω S J _hcompat]
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hcompat : IsCompatibleACS S J) :
-- imply
  ∃ (fam : ApproxHolomorphicSectionFamily (inst := inst)), IsUniformlyBounded fam ∧ IsApproxHolomorphic fam ∧ IsUniformlyConcentrated fam ∧ (∃ (pe : PointwiseEval Ω VF) (md : ManifoldDist VF) (c : ℝ), c > 0 ∧ ∀ (k : ℕ) (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) → c ≤ pe.peval q (fam.section_ k p)) := by
-- proof
  let gpd := HasGaussianPeakData.peakData (S := S) (J := J) (hcompat := _hcompat)
  let fam : ApproxHolomorphicSectionFamily (inst := inst) :=
    { L := gpd.L
      section_ := gpd.section_ }
  have hUB : IsUniformlyBounded fam := ⟨⟨gpd.wdn, gpd.uniform_bound⟩⟩
  have hAH : IsApproxHolomorphic fam := by
    constructor
    · exact gpd.delbar_exact
    · obtain ⟨C, hC_pos, hC_bound⟩ := gpd.delbar_l2_decay
      exact ⟨gpd.l2, C, hC_pos, hC_bound⟩
  have hUC : IsUniformlyConcentrated fam := by
    constructor
    · exact gpd.concentrated
    · obtain ⟨C_gd, lam, N, hCgd_pos, hlam_pos, hgd_bound⟩ := gpd.gaussian_decay
      exact ⟨gpd.pe, gpd.md, C_gd, lam, N, hCgd_pos, hlam_pos, hgd_bound⟩
    · exact ⟨gpd.wdn, gpd.uniform_bound⟩
  have hLB : ∃ (pe : PointwiseEval Ω VF) (md : ManifoldDist VF) (c : ℝ), c > 0 ∧
    ∀ (k : ℕ) (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
      c ≤ pe.peval q (fam.section_ k p) := by
    obtain ⟨c, hc_pos, hc_bound⟩ := gpd.local_lower_bound
    exact ⟨gpd.pe, gpd.md, c, hc_pos, hc_bound⟩
  exact ⟨fam, hUB, hAH, hUC, hLB⟩

/--
[donaldson_prop1_legacy_internal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma donaldson_prop1_legacy_internal
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  [hpd : HasDonaldsonProofData Ω S J _hcompat]
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler S J)
  (_hcompat : IsCompatibleACS S J) :
-- imply
  ∃ (k₀ : ℕ) (pe : PointwiseEval Ω VF) (md : ManifoldDist VF) (fam : ApproxHolomorphicSectionFamily (inst := inst)), 1 ≤ k₀ ∧ IsUniformlyBounded fam ∧ IsApproxHolomorphic fam ∧ IsUniformlyConcentrated fam ∧ (∃ (c : ℝ), c > 0 ∧ ∀ (k : ℕ), k₀ < k → ∀ (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) → c ≤ pe.peval q (fam.section_ k p)) ∧ (∃ (fam' : ApproxHolomorphicSectionFamily (inst := inst)), IsHolomorphicFamily hpd.dol fam' ∧ IsExponentiallyCloseCubeRoot hpd.wdn fam fam') := by
-- proof
  let wdn := hpd.wdn
  let l2 := hpd.l2
  let dol := hpd.dol
  letI : HasGaussianPeakData Ω S J _hcompat := hpd.gaussianPeakInst
  letI : HasWeitzenbockDecomp Ω l2 dol := hpd.weitzenbockInst
  letI : HasDonaldsonPDEData Ω wdn l2 dol := hpd.pdeDataInst
  obtain ⟨fam, hbound, happrox, hconc, pe, md, c, hc_pos, hpeak⟩ :=
    gaussian_peak_sections_exist_sorry S J _hcompat
  refine ⟨1, pe, md, fam, le_refl 1, hbound, happrox, hconc,
    ⟨c, hc_pos, fun k _hk p q hdist => hpeak k p q hdist⟩, ?_⟩
  have h_gci : GreenCorrectionInput wdn l2 dol fam :=
    green_correction_data_sorry wdn l2 dol fam
  let fam' := correctedFamily wdn l2 dol fam h_gci
  have h_hol : IsHolomorphicFamily dol fam' :=
    green_corrected_family_is_holomorphic wdn l2 dol fam h_gci
  have h_exp : IsExponentiallyCloseCubeRoot wdn fam fam' :=
    green_correction_exp_close wdn l2 dol fam h_gci
  exact ⟨fam', h_hol, h_exp⟩

/--
[donaldson_gaussian_peak_sections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma donaldson_gaussian_peak_sections
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  [HasGaussianPeakData Ω S J _hcompat]
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler S J)
  (_hcompat : IsCompatibleACS S J) :
-- imply
  ∃ (fam : ApproxHolomorphicSectionFamily (inst := inst)), IsUniformlyBounded fam ∧ IsApproxHolomorphic fam ∧ IsUniformlyConcentrated fam ∧ (∃ (pe : PointwiseEval Ω VF) (md : ManifoldDist VF) (c : ℝ), c > 0 ∧ ∀ (k : ℕ) (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) → c ≤ pe.peval q (fam.section_ k p)) :=
-- proof
  gaussian_peak_sections_exist_sorry S J _hcompat

/--
[donaldson_proposition_1_with_hypotheses](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma donaldson_proposition_1_with_hypotheses
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
-- given
  (J : AlmostComplexStr (inst := inst))
  (hK : IsKahler S J)
  (hcompat : IsCompatibleACS S J)
  (wdn : WeightedDerivSupNorm Ω (inst := inst))
  (l2 : L2NormSpace Ω (inst := inst))
  (dol : DolbeaultOps (inst := inst))
  (h_normal_coords : ∃ (nls : NormalizedLocalSectionData (inst := inst)), IsUniformlyConcentrated nls.fam ∧ IsUniformlyBounded nls.fam ∧ IsApproxHolomorphic nls.fam ∧ (∃ (c : ℝ), c > 0 ∧ ∀ (k : ℕ), nls.k₀ < k → ∀ (p q : VF), nls.md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) → c ≤ nls.pe.peval q (nls.fam.section_ k p)))
  (h_cutoff : ∀ (nls : NormalizedLocalSectionData (inst := inst)), ∃ (C_g lam : ℝ), C_g > 0 ∧ lam > 0 ∧ ∀ (k : ℕ) (p : VF), l2.l2norm (dol.delbar (nls.fam.section_ k p)) ≤ C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)))
  (h_curvature : Σ' (greenCorrection : ℕ → Ω 0 → Ω 0) (C_geom : ℝ), C_geom > 0 ∧ (∀ (k : ℕ) (s : Ω 0), (k : ℝ) > C_geom → l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤ 1 / ((k : ℝ) - C_geom) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))) ∧ (∀ (k : ℕ), k ≠ 0 → ∀ (s : Ω 0), ∃ (B : ℝ), B > 0 ∧ l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤ B * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))))
  (h_hodge : ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0), dol.delbar (s + h_curvature.1 k s) = 0)
  (h_cauchy : (∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧ ∀ (k : ℕ) (s : Ω 0), wdn.weighted_supnorm k r (h_curvature.1 k s) ≤ C_r * l2.l2norm (dol.delbar s)) ∧ (∀ (s : Ω 0), dol.delbar (s + h_curvature.1 0 s) = 0)) :
-- imply
  ∃ (k₀ : ℕ) (pe : PointwiseEval Ω VF) (md : ManifoldDist VF) (fam : ApproxHolomorphicSectionFamily (inst := inst)), 1 ≤ k₀ ∧ IsUniformlyBounded fam ∧ IsApproxHolomorphic fam ∧ IsUniformlyConcentrated fam ∧ (∃ (c : ℝ), c > 0 ∧ ∀ (k : ℕ), k₀ < k → ∀ (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) → c ≤ pe.peval q (fam.section_ k p)) ∧ (∃ (fam' : ApproxHolomorphicSectionFamily (inst := inst)), IsHolomorphicFamily dol fam' ∧ IsExponentiallyCloseCubeRoot wdn fam fam') := by
-- proof
  obtain ⟨nls, hconc, hbound, happrox, hpeak⟩ := h_normal_coords
  obtain ⟨C_g, lam, hCg, hlam, hdelbar_decay⟩ := h_cutoff nls
  let hG : HasGreenOperator Ω l2 dol :=
    { greenCorrection := h_curvature.1
      green_holomorphic := h_hodge
      green_l2_sq_bound :=
        spectral_gap_from_curvature_bound l2 dol h_curvature.1
          h_curvature.2.1 h_curvature.2.2.1 h_curvature.2.2.2.1 h_curvature.2.2.2.2 }
  obtain ⟨hCrBound, hHolZero⟩ := h_cauchy
  let fam := nls.fam
  let fam' : ApproxHolomorphicSectionFamily (inst := inst) :=
    { L := fam.L
      section_ := fun k p => fam.section_ k p + hG.greenCorrection k (fam.section_ k p) }
  have hhol_sections : ∀ (k : ℕ) (p : VF), dol.delbar (fam'.section_ k p) = 0 := by
    intro k p
    by_cases hk : k = 0
    · subst hk; exact hHolZero (fam.section_ 0 p)
    · exact hG.green_holomorphic k hk (fam.section_ k p)
  have hcr_close : ∀ (r : ℕ), ∃ (C'_r : ℝ), C'_r > 0 ∧
    ∀ (k : ℕ) (p : VF),
      wdn.weighted_supnorm k r (fam.section_ k p - fam'.section_ k p) ≤
        C'_r * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by
    intro r
    obtain ⟨C_r, hCr_pos, hCr⟩ := hCrBound r
    refine ⟨C_r * C_g, mul_pos hCr_pos hCg, ?_⟩
    intro k p
    have h_diff : fam.section_ k p - fam'.section_ k p =
      -(hG.greenCorrection k (fam.section_ k p)) := by
      show fam.section_ k p - (fam.section_ k p + hG.greenCorrection k (fam.section_ k p)) =
        -(hG.greenCorrection k (fam.section_ k p))
      abel
    rw [h_diff]
    have h_neg := wdn.weighted_supnorm_neg k r (hG.greenCorrection k (fam.section_ k p))
    have h_cr := hCr k (fam.section_ k p)
    have h_decay := hdelbar_decay k p
    calc wdn.weighted_supnorm k r (-(hG.greenCorrection k (fam.section_ k p)))
      ≤ wdn.weighted_supnorm k r (hG.greenCorrection k (fam.section_ k p)) := h_neg
      _ ≤ C_r * l2.l2norm (dol.delbar (fam.section_ k p)) := h_cr
      _ ≤ C_r * (C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) := by
        apply mul_le_mul_of_nonneg_left h_decay (le_of_lt hCr_pos)
      _ = C_r * C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by ring
  refine ⟨nls.k₀, nls.pe, nls.md, fam, nls.hk₀, hbound, happrox, hconc, hpeak, fam', ?_, ?_⟩
  · exact ⟨hhol_sections⟩
  · exact ⟨rfl, lam, hlam, hcr_close⟩
set_option maxHeartbeats 800000 in

/--
[donaldson_proposition_1_book](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
lemma donaldson_proposition_1_book
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
-- given
  (J : AlmostComplexStr (inst := inst))
  (hK : IsKahler S J)
  (hcompat : IsCompatibleACS S J)
  (wdn : WeightedDerivSupNorm Ω (inst := inst))
  (l2 : L2NormSpace Ω (inst := inst))
  (dol : DolbeaultOps (inst := inst))
  (h_normal_coords : ∃ (nls : NormalizedLocalSectionData (inst := inst)), IsUniformlyConcentrated nls.fam ∧ IsUniformlyBounded nls.fam ∧ IsApproxHolomorphic nls.fam ∧ (∃ (c : ℝ), c > 0 ∧ ∀ (k : ℕ), nls.k₀ < k → ∀ (p q : VF), nls.md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) → c ≤ nls.pe.peval q (nls.fam.section_ k p)))
  (h_cutoff : ∀ (nls : NormalizedLocalSectionData (inst := inst)), ∃ (C_g lam : ℝ), C_g > 0 ∧ lam > 0 ∧ ∀ (k : ℕ) (p : VF), l2.l2norm (dol.delbar (nls.fam.section_ k p)) ≤ C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)))
  (h_curvature : Σ' (greenCorrection : ℕ → Ω 0 → Ω 0) (C_geom : ℝ), C_geom > 0 ∧ (∀ (k : ℕ) (s : Ω 0), (k : ℝ) > C_geom → l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤ 1 / ((k : ℝ) - C_geom) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))) ∧ (∀ (k : ℕ), k ≠ 0 → ∀ (s : Ω 0), ∃ (B : ℝ), B > 0 ∧ l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤ B * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))))
  (h_hodge : ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0), dol.delbar (s + h_curvature.1 k s) = 0)
  (h_cauchy : (∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧ ∀ (k : ℕ) (s : Ω 0), wdn.weighted_supnorm k r (h_curvature.1 k s) ≤ C_r * l2.l2norm (dol.delbar s)) ∧ (∀ (s : Ω 0), dol.delbar (s + h_curvature.1 0 s) = 0)) :
-- imply
  ∃ (k₀ : ℕ) (pe : PointwiseEval Ω VF) (md : ManifoldDist VF) (fam : ApproxHolomorphicSectionFamily (inst := inst)), 1 ≤ k₀ ∧ IsUniformlyBounded fam ∧ IsApproxHolomorphic fam ∧ IsUniformlyConcentrated fam ∧ (∃ (c : ℝ), c > 0 ∧ ∀ (k : ℕ), k₀ < k → ∀ (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) → c ≤ pe.peval q (fam.section_ k p)) ∧ (∃ (fam' : ApproxHolomorphicSectionFamily (inst := inst)), IsHolomorphicFamily dol fam' ∧ IsExponentiallyCloseCubeRoot wdn fam fam') := by
-- proof
  obtain ⟨nls, hconc, hbound, happrox, hpeak⟩ := h_normal_coords
  obtain ⟨C_g, lam, hCg, hlam, hdelbar_decay⟩ := h_cutoff nls
  let hG : HasGreenOperator Ω l2 dol :=
    { greenCorrection := h_curvature.1
      green_holomorphic := h_hodge
      green_l2_sq_bound :=
        spectral_gap_from_curvature_bound l2 dol h_curvature.1
          h_curvature.2.1 h_curvature.2.2.1 h_curvature.2.2.2.1 h_curvature.2.2.2.2 }
  obtain ⟨hCrBound, hHolZero⟩ := h_cauchy
  let fam := nls.fam
  let fam' : ApproxHolomorphicSectionFamily (inst := inst) :=
    { L := fam.L
      section_ := fun k p => fam.section_ k p + hG.greenCorrection k (fam.section_ k p) }
  have hhol_sections : ∀ (k : ℕ) (p : VF), dol.delbar (fam'.section_ k p) = 0 := by
    intro k p
    by_cases hk : k = 0
    · subst hk; exact hHolZero (fam.section_ 0 p)
    · exact hG.green_holomorphic k hk (fam.section_ k p)
  have hcr_close : ∀ (r : ℕ), ∃ (C'_r : ℝ), C'_r > 0 ∧
    ∀ (k : ℕ) (p : VF),
      wdn.weighted_supnorm k r (fam.section_ k p - fam'.section_ k p) ≤
        C'_r * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by
    intro r
    obtain ⟨C_r, hCr_pos, hCr⟩ := hCrBound r
    refine ⟨C_r * C_g, mul_pos hCr_pos hCg, ?_⟩
    intro k p
    have h_diff : fam.section_ k p - fam'.section_ k p =
      -(hG.greenCorrection k (fam.section_ k p)) := by
      show fam.section_ k p - (fam.section_ k p + hG.greenCorrection k (fam.section_ k p)) =
        -(hG.greenCorrection k (fam.section_ k p))
      abel
    rw [h_diff]
    have h_neg := wdn.weighted_supnorm_neg k r (hG.greenCorrection k (fam.section_ k p))
    have h_cr := hCr k (fam.section_ k p)
    have h_decay := hdelbar_decay k p
    calc wdn.weighted_supnorm k r (-(hG.greenCorrection k (fam.section_ k p)))
      ≤ wdn.weighted_supnorm k r (hG.greenCorrection k (fam.section_ k p)) := h_neg
      _ ≤ C_r * l2.l2norm (dol.delbar (fam.section_ k p)) := h_cr
      _ ≤ C_r * (C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) := by
        apply mul_le_mul_of_nonneg_left h_decay (le_of_lt hCr_pos)
      _ = C_r * C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by ring
  refine ⟨nls.k₀, nls.pe, nls.md, fam, nls.hk₀, hbound, happrox, hconc, hpeak, fam', ?_, ?_⟩
  · exact ⟨hhol_sections⟩
  · exact ⟨rfl, lam, hlam, hcr_close⟩

/--
[l2_bound_from_squared_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma l2_bound_from_squared_bound_eq
  {a b C : ℝ}
  {k : ℕ}
-- given
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hCk : 0 ≤ C / (k : ℝ))
  (hsq : a * a ≤ C / (k : ℝ) * (b * b)) :
-- imply
  a ≤ Real.sqrt (C / (k : ℝ)) * b := by
-- proof
  apply l2_bound_from_squared_bound ha hb hCk hsq

/--
[derive_correction_l2_exp_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma derive_correction_l2_exp_bound_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  {l2 : L2NormSpace Ω (inst := inst)}
  {dol : DolbeaultOps (inst := inst)}
  {greenOp : HasGreenOperator Ω l2 dol}
  {fam : ApproxHolomorphicSectionFamily (inst := inst)}
  {c_G : ℝ}
  {C_g : ℝ}
  {lam : ℝ}
-- given
  (hcG_pos : c_G > 0)
  (h_green_sq : ∀ (k : ℕ) (hk : k ≠ 0) (s : Ω 0), l2.l2norm (greenOp.greenCorrection k s) * l2.l2norm (greenOp.greenCorrection k s) ≤ c_G / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s)))
  (hCg_pos : C_g > 0)
  (hlam_pos : lam > 0)
  (h_gauss : ∀ (k : ℕ) (p : VF), l2.l2norm (dol.delbar (fam.section_ k p)) ≤ C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)))
  (h_zero : ∀ (p : VF), l2.l2norm (greenOp.greenCorrection 0 (fam.section_ 0 p)) ≤ Real.sqrt c_G * C_g * Real.exp (-lam * (0 : ℝ) ^ ((1 : ℝ) / 3))) :
-- imply
  ∃ (C_l2 : ℝ) (lam_l2 : ℝ), C_l2 > 0 ∧ lam_l2 > 0 ∧ ∀ (k : ℕ) (p : VF), l2.l2norm (greenOp.greenCorrection k (fam.section_ k p)) ≤ C_l2 * Real.exp (-lam_l2 * (k : ℝ) ^ ((1 : ℝ) / 3)) := by
-- proof
  apply derive_correction_l2_exp_bound c_G hcG_pos h_green_sq C_g lam hCg_pos hlam_pos h_gauss h_zero

/--
[weitzenbock_uniform_constant_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma weitzenbock_uniform_constant_pos_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [wb : HasWeitzenbockDecomp Ω l2 dol]
-- given
  (l2 : L2NormSpace Ω (inst := inst))
  (dol : DolbeaultOps (inst := inst)) :
-- imply
  weitzenbock_uniform_constant_axiom l2 dol > 0 := by
-- proof
  apply weitzenbock_uniform_constant_pos l2 dol

/--
[weitzenbock_uniform_l2_bound_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma weitzenbock_uniform_l2_bound_axiom_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [wb : HasWeitzenbockDecomp Ω l2 dol]
-- given
  (l2 : L2NormSpace Ω (inst := inst))
  (dol : DolbeaultOps (inst := inst)) :
-- imply
  ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0), l2.l2norm ((weitzenbock_green_operator_axiom l2 dol).greenCorrection k s) * l2.l2norm ((weitzenbock_green_operator_axiom l2 dol).greenCorrection k s) ≤ (weitzenbock_uniform_constant_axiom l2 dol) / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s)) := by
-- proof
  apply weitzenbock_uniform_l2_bound_axiom l2 dol

/--
[mul_exp_neg_le_exp_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma mul_exp_neg_le_exp_neg_one_eq
  {y : ℝ} :
-- imply
  y * Real.exp (-y) ≤ Real.exp (-1) := by
-- proof
  apply mul_exp_neg_le_exp_neg_one y

/--
[t_exp_neg_lam_t_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma t_exp_neg_lam_t_bound_eq
  {t lam : ℝ}
-- given
  (hlam_pos : lam > 0) :
-- imply
  t * Real.exp (-lam * t) ≤ 1 / (lam * Real.exp 1) := by
-- proof
  apply t_exp_neg_lam_t_bound t lam hlam_pos

/--
[absorb_poly_into_exp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma absorb_poly_into_exp_eq
  {A lam0 : ℝ}
-- given
  (hA : A > 0)
  (hlam0 : lam0 > 0) :
-- imply
  ∃ (C_g lam : ℝ), C_g > 0 ∧ lam > 0 ∧ ∀ (t : ℝ), 0 ≤ t → A * t * Real.exp (-lam0 * t) ≤ C_g * Real.exp (-lam * t) := by
-- proof
  apply absorb_poly_into_exp A lam0 hA hlam0

/--
[derive_gaussian_l2_bound'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma derive_gaussian_l2_bound'_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  {l2 : L2NormSpace Ω (inst := inst)}
  {dol : DolbeaultOps (inst := inst)}
  {fam : ApproxHolomorphicSectionFamily (inst := inst)}
  {cgd : CutoffGaussianData l2 dol fam} :
-- imply
  ∃ (C_g : ℝ) (lam : ℝ), C_g > 0 ∧ lam > 0 ∧ ∀ (k : ℕ) (p : VF), l2.l2norm (dol.delbar (fam.section_ k p)) ≤ C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by
-- proof
  apply derive_gaussian_l2_bound' cgd

/--
[cauchy_estimates_for_green_op'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma cauchy_estimates_for_green_op'_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasWeitzenbockDecomp Ω l2 dol]
  [hpde : HasDonaldsonPDEData Ω wdn l2 dol]
  {greenOp : HasGreenOperator Ω l2 dol}
-- given
  (wdn : WeightedDerivSupNorm Ω (inst := inst))
  (l2 : L2NormSpace Ω (inst := inst))
  (dol : DolbeaultOps (inst := inst)) :
-- imply
  ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧ ∀ (k : ℕ) (s : Ω 0), wdn.weighted_supnorm k r (greenOp.greenCorrection k s) ≤ C_r * l2.l2norm (greenOp.greenCorrection k s) := by
-- proof
  apply cauchy_estimates_for_green_op' wdn l2 dol greenOp

/--
[gaussian_decay_delbar_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma gaussian_decay_delbar_axiom_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasWeitzenbockDecomp Ω l2 dol]
  [HasDonaldsonPDEData Ω wdn l2 dol]
-- given
  (wdn : WeightedDerivSupNorm Ω (inst := inst))
  (l2 : L2NormSpace Ω (inst := inst))
  (dol : DolbeaultOps (inst := inst))
  (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
-- imply
  ∃ (C_g : ℝ) (lam : ℝ), C_g > 0 ∧ lam > 0 ∧ ∀ (k : ℕ) (p : VF), l2.l2norm (dol.delbar (fam.section_ k p)) ≤ C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by
-- proof
  apply gaussian_decay_delbar_axiom wdn l2 dol fam

/--
[cauchy_estimates_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma cauchy_estimates_axiom_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasWeitzenbockDecomp Ω l2 dol]
  [HasDonaldsonPDEData Ω wdn l2 dol]
-- given
  (wdn : WeightedDerivSupNorm Ω (inst := inst))
  (l2 : L2NormSpace Ω (inst := inst))
  (dol : DolbeaultOps (inst := inst)) :
-- imply
  ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧ ∀ (k : ℕ) (s : Ω 0), wdn.weighted_supnorm k r ((weitzenbock_green_operator_axiom l2 dol).greenCorrection k s) ≤ C_r * l2.l2norm ((weitzenbock_green_operator_axiom l2 dol).greenCorrection k s) := by
-- proof
  apply cauchy_estimates_axiom wdn l2 dol

/--
[correction_hol_at_zero_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma correction_hol_at_zero_axiom_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasWeitzenbockDecomp Ω l2 dol]
  [hpde : HasDonaldsonPDEData Ω _wdn l2 dol]
-- given
  (_wdn : WeightedDerivSupNorm Ω (inst := inst))
  (l2 : L2NormSpace Ω (inst := inst))
  (dol : DolbeaultOps (inst := inst))
  (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
-- imply
  ∀ (p : VF), dol.delbar (fam.section_ 0 p + (weitzenbock_green_operator_axiom l2 dol).greenCorrection 0 (fam.section_ 0 p)) = 0 := by
-- proof
  apply correction_hol_at_zero_axiom _wdn l2 dol fam

/--
[correction_bundle_eq_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma correction_bundle_eq_axiom_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
-- given
  (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
-- imply
  fam.L = correction_bundle_data_axiom fam := by
-- proof
  apply correction_bundle_eq_axiom fam

/--
[correction_l2_zero_edge_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma correction_l2_zero_edge_axiom_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasWeitzenbockDecomp Ω l2 dol]
  [hpde : HasDonaldsonPDEData Ω _wdn l2 dol]
  {c_G : ℝ}
  {C_g : ℝ}
  {lam : ℝ}
-- given
  (_wdn : WeightedDerivSupNorm Ω (inst := inst))
  (l2 : L2NormSpace Ω (inst := inst))
  (dol : DolbeaultOps (inst := inst))
  (fam : ApproxHolomorphicSectionFamily (inst := inst))
  (_hCg_pos : C_g > 0)
  (_hlam_pos : lam > 0)
  (_h_gauss : ∀ (k : ℕ) (p : VF), l2.l2norm (dol.delbar (fam.section_ k p)) ≤ C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) :
-- imply
  ∀ (p : VF), l2.l2norm ((weitzenbock_green_operator_axiom l2 dol).greenCorrection 0 (fam.section_ 0 p)) ≤ Real.sqrt c_G * C_g * Real.exp (-lam * (0 : ℝ) ^ ((1 : ℝ) / 3)) := by
-- proof
  apply correction_l2_zero_edge_axiom _wdn l2 dol fam c_G C_g lam _hCg_pos _hlam_pos _h_gauss

/--
[correction_l2_exp_bound_from_spectral_gap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean)
-/
@[path]
private lemma correction_l2_exp_bound_from_spectral_gap_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  {pde : GreenCorrectionPDEAxioms wdn l2 dol fam}
-- given
  (wdn : WeightedDerivSupNorm Ω (inst := inst))
  (l2 : L2NormSpace Ω (inst := inst))
  (dol : DolbeaultOps (inst := inst))
  (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
-- imply
  ∃ (C_l2 : ℝ) (lam_l2 : ℝ), C_l2 > 0 ∧ lam_l2 > 0 ∧ ∀ (k : ℕ) (p : VF), l2.l2norm (pde.greenCorrection k (fam.section_ k p)) ≤ C_l2 * Real.exp (-lam_l2 * (k : ℝ) ^ ((1 : ℝ) / 3)) := by
-- proof
  apply correction_l2_exp_bound_from_spectral_gap wdn l2 dol fam pde


-- created on 2026-10-23
