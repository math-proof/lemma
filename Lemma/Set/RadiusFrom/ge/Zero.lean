import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.BruhatTitsFixedPoint
open Set Filter Topology


/--
[radiusFrom_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BruhatTitsFixedPoint.lean)
-/
@[path]
lemma radiusFrom_nonneg
  [MetricSpace M]
  {x : M}
  {Y : Set M} :
-- imply
  0 ≤ radiusFrom x Y := by
-- proof
  unfold radiusFrom
  exact Real.sSup_nonneg (by rintro _ ⟨⟨_, _⟩, rfl⟩; exact dist_nonneg)

/--
[bddAbove_dist_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BruhatTitsFixedPoint.lean)
-/
@[path]
lemma bddAbove_dist_range
  [MetricSpace M]
  {x : M}
  {Y : Set M}
-- given
  (hbd : Bornology.IsBounded Y) :
-- imply
  BddAbove (range (fun (y : Y) => dist x (y : M))) := by
-- proof
  obtain ⟨r, hr⟩ := hbd.subset_ball x
  refine ⟨r, ?_⟩
  rintro _ ⟨⟨y, hy⟩, rfl⟩
  simp only
  have := Metric.mem_ball.mp (hr hy)
  linarith [dist_comm x y]

/--
[dist_le_radiusFrom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BruhatTitsFixedPoint.lean)
-/
@[path]
lemma dist_le_radiusFrom
  [MetricSpace M]
  {x : M}
  {Y : Set M}
  {y : M}
-- given
  (hbd : Bornology.IsBounded Y)
  (hy : y ∈ Y) :
-- imply
  dist x y ≤ radiusFrom x Y :=
-- proof
  le_ciSup (bddAbove_dist_range x Y hbd) ⟨y, hy⟩

/--
[circumradius_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BruhatTitsFixedPoint.lean)
-/
@[path]
lemma circumradius_nonneg
  [MetricSpace M]
  {Y : Set M} :
-- imply
  0 ≤ circumradius Y := by
-- proof
  unfold circumradius
  show 0 ≤ sInf (range (fun x => radiusFrom x Y))
  exact Real.sInf_nonneg (by rintro _ ⟨x, rfl⟩; exact radiusFrom_nonneg x Y)

/--
[circumradius_le_radiusFrom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BruhatTitsFixedPoint.lean)
-/
@[path]
lemma circumradius_le_radiusFrom
  [MetricSpace M]
  {x : M}
  {Y : Set M} :
-- imply
  circumradius Y ≤ radiusFrom x Y :=
-- proof
  ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact radiusFrom_nonneg z Y⟩ x

/--
[isometry_radiusFrom_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BruhatTitsFixedPoint.lean)
-/
@[path]
lemma isometry_radiusFrom_eq
  [MetricSpace M]
  {φ : M → M}
  {x : M}
  {Y : Set M}
-- given
  (hφ : Isometry φ) :
-- imply
  radiusFrom (φ x) (φ '' Y) = radiusFrom x Y := by
-- proof
  unfold radiusFrom
  show sSup (range (fun (z : ↥(φ '' Y)) => dist (φ x) (z : M))) =
    sSup (range (fun (y : ↥Y) => dist x (y : M)))
  congr 1
  ext d; simp only [mem_range, Subtype.exists]
  constructor
  · rintro ⟨z, hz, rfl⟩; obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨y, hy, (hφ.dist_eq x y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨φ y, mem_image_of_mem φ hy, hφ.dist_eq x y⟩

/--
[circumcenter_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BruhatTitsFixedPoint.lean)
-/
@[path]
lemma circumcenter_exists
  [MetricSpace M]
  {M : Type*}
  [MetricSpace M]
  [CompleteSpace M]
  {Y : Set M}
-- given
  (hNCI : NegativeCurvatureInequality M)
  (hne : Y.Nonempty)
  (hbd : Bornology.IsBounded Y) :
-- imply
  ∃ c : M, IsCircumcenter c Y := by
-- proof
  obtain ⟨y₀, hy₀⟩ := hne
  haveI : Nonempty M := ⟨y₀⟩
  haveI : Nonempty ↥Y := ⟨⟨y₀, hy₀⟩⟩
  set r := circumradius Y with hr_def
  have hr_nn : 0 ≤ r := circumradius_nonneg Y
  have hmini : ∀ n : ℕ, ∃ x : M, radiusFrom x Y < r + 1 / ((n : ℝ) + 1) := by
    intro n; apply exists_lt_of_ciInf_lt
    show (⨅ x : M, radiusFrom x Y) < r + 1 / ((n : ℝ) + 1)
    simp only [hr_def, circumradius]
    linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
  choose xseq hxseq using hmini
  have hdist_bound : ∀ i j : ℕ, dist (xseq i) (xseq j) ^ 2 ≤
    2 * (r + 1 / ((i : ℝ) + 1)) ^ 2 + 2 * (r + 1 / ((j : ℝ) + 1)) ^ 2 - 4 * r ^ 2 := by
    intro i j
    obtain ⟨mid, hmid⟩ := hNCI (xseq i) (xseq j)
    have bound : ∀ y ∈ Y, dist y mid ^ 2 ≤
      (1/2) * (r + 1/((i : ℝ)+1))^2 + (1/2) * (r + 1/((j : ℝ)+1))^2 -
      (1/4) * dist (xseq i) (xseq j) ^ 2 := by
      intro y hy
      have h1 : dist y (xseq i) ≤ r + 1/((i : ℝ)+1) := by
        calc dist y (xseq i) = dist (xseq i) y := dist_comm _ _
          _ ≤ radiusFrom (xseq i) Y := dist_le_radiusFrom _ hbd hy
          _ ≤ r + 1/((i : ℝ)+1) := le_of_lt (hxseq i)
      have h2 : dist y (xseq j) ≤ r + 1/((j : ℝ)+1) := by
        calc dist y (xseq j) = dist (xseq j) y := dist_comm _ _
          _ ≤ radiusFrom (xseq j) Y := dist_le_radiusFrom _ hbd hy
          _ ≤ r + 1/((j : ℝ)+1) := le_of_lt (hxseq j)
      nlinarith [hmid y, sq_nonneg (r + 1/((i:ℝ)+1) - dist y (xseq i)),
        sq_nonneg (r + 1/((j:ℝ)+1) - dist y (xseq j)),
        @dist_nonneg M _ y (xseq i), @dist_nonneg M _ y (xseq j)]
    have hnn : 0 ≤ (1/2) * (r + 1/((i : ℝ)+1))^2 + (1/2) * (r + 1/((j : ℝ)+1))^2 -
      (1/4) * dist (xseq i) (xseq j) ^ 2 := by
      nlinarith [bound y₀ hy₀, sq_nonneg (dist y₀ mid)]
    have hrad_mid : radiusFrom mid Y ≤ Real.sqrt ((1/2) * (r + 1/((i : ℝ)+1))^2 +
      (1/2) * (r + 1/((j : ℝ)+1))^2 - (1/4) * dist (xseq i) (xseq j) ^ 2) := by
      unfold radiusFrom; apply ciSup_le; intro ⟨y, hy⟩
      rw [Real.le_sqrt dist_nonneg hnn, dist_comm]; exact bound y hy
    have hcr_mid : r ≤ radiusFrom mid Y := circumradius_le_radiusFrom mid Y
    have h_comb := le_trans hcr_mid hrad_mid
    rw [Real.le_sqrt hr_nn hnn] at h_comb
    nlinarith
  have hcauchy : CauchySeq xseq := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
    obtain ⟨N, hN⟩ := exists_nat_gt ((8 * r + 4) / ε ^ 2)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [show ε = Real.sqrt (ε ^ 2) by rw [Real.sqrt_sq (le_of_lt hε)]]
    rw [← Real.sqrt_sq dist_nonneg]
    apply Real.sqrt_lt_sqrt (sq_nonneg _)
    have hm_le : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by positivity)
      exact_mod_cast Nat.succ_le_succ hm
    have hn_le : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by positivity)
      exact_mod_cast Nat.succ_le_succ hn
    have diff_m : (1/((N:ℝ)+1) - 1/((m:ℝ)+1)) * (2*r + 1/((N:ℝ)+1) + 1/((m:ℝ)+1)) ≥ 0 := by
      apply mul_nonneg <;> [linarith; positivity]
    have diff_n : (1/((N:ℝ)+1) - 1/((n:ℝ)+1)) * (2*r + 1/((N:ℝ)+1) + 1/((n:ℝ)+1)) ≥ 0 := by
      apply mul_nonneg <;> [linarith; positivity]
    calc dist (xseq m) (xseq n) ^ 2
      ≤ 2 * (r + 1/((m : ℝ)+1))^2 + 2 * (r + 1/((n : ℝ)+1))^2 - 4 * r^2 := hdist_bound m n
      _ ≤ 2 * (r + 1/((N : ℝ)+1))^2 + 2 * (r + 1/((N : ℝ)+1))^2 - 4 * r^2 := by nlinarith
      _ = 4 * (r + 1/((N : ℝ)+1))^2 - 4 * r^2 := by ring
      _ < ε ^ 2 := by
        have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        have key : 8 * r + 4 < (N : ℝ) * ε ^ 2 := by rwa [div_lt_iff₀ hε2] at hN
        have expand : 4 * (r + 1 / ((N : ℝ) + 1)) ^ 2 - 4 * r ^ 2 =
          (8 * r * ((N : ℝ) + 1) + 4) / ((N : ℝ) + 1) ^ 2 := by field_simp; ring
        rw [expand, div_lt_iff₀ (by positivity : (0:ℝ) < ((N : ℝ) + 1) ^ 2)]
        nlinarith [sq_nonneg ((N : ℝ) + 1), sq_nonneg (N : ℝ)]
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨c, ?_⟩
  unfold IsCircumcenter
  apply le_antisymm
  ·
    unfold radiusFrom; apply ciSup_le; intro ⟨y, hy⟩
    exact le_of_tendsto_of_tendsto
      (hc.dist tendsto_const_nhds)
      (by have h := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
        have := Filter.Tendsto.add (show Tendsto (fun _ : ℕ => r) atTop (nhds r) from
          tendsto_const_nhds) h
        rwa [add_zero] at this)
      (Filter.Eventually.of_forall fun n => le_of_lt (calc
        dist (xseq n) y ≤ radiusFrom (xseq n) Y := dist_le_radiusFrom _ hbd hy
        _ < r + 1 / ((n : ℝ) + 1) := hxseq n))
  ·
    exact circumradius_le_radiusFrom c Y

/--
[circumcenter_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BruhatTitsFixedPoint.lean)
-/
@[path]
lemma circumcenter_unique
  [MetricSpace M]
  {M : Type*}
  [MetricSpace M]
  {Y : Set M}
  {c₁ c₂ : M}
-- given
  (hNCI : NegativeCurvatureInequality M)
  (hne : Y.Nonempty)
  (hbd : Bornology.IsBounded Y)
  (h₁ : IsCircumcenter c₁ Y)
  (h₂ : IsCircumcenter c₂ Y) :
-- imply
  c₁ = c₂ := by
-- proof
  by_contra hne_pts
  obtain ⟨y₀, hy₀⟩ := hne
  haveI : Nonempty ↥Y := ⟨⟨y₀, hy₀⟩⟩
  set r := circumradius Y
  have hr_nn : 0 ≤ r := circumradius_nonneg Y
  have hd : 0 < dist c₁ c₂ := dist_pos.mpr hne_pts
  obtain ⟨mid, hmid⟩ := hNCI c₁ c₂
  have hc1 : ∀ y ∈ Y, dist y c₁ ≤ r := fun y hy => by
    rw [dist_comm]; exact le_trans (dist_le_radiusFrom c₁ hbd hy) (le_of_eq h₁)
  have hc2 : ∀ y ∈ Y, dist y c₂ ≤ r := fun y hy => by
    rw [dist_comm]; exact le_trans (dist_le_radiusFrom c₂ hbd hy) (le_of_eq h₂)
  have hbd_mid : ∀ y ∈ Y, dist y mid ^ 2 ≤ r ^ 2 - (1/4) * dist c₁ c₂ ^ 2 := by
    intro y hy
    have sq1 : dist y c₁ ^ 2 ≤ r ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (hc1 y hy) (@dist_nonneg M _ y c₁)]
    have sq2 : dist y c₂ ^ 2 ≤ r ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (hc2 y hy) (@dist_nonneg M _ y c₂)]
    nlinarith [hmid y]
  have hnn : 0 ≤ r ^ 2 - (1/4) * dist c₁ c₂ ^ 2 := by
    nlinarith [hbd_mid y₀ hy₀, sq_nonneg (dist y₀ mid)]
  have hrf_mid : radiusFrom mid Y ≤ Real.sqrt (r ^ 2 - (1/4) * dist c₁ c₂ ^ 2) := by
    unfold radiusFrom; apply ciSup_le; intro ⟨y, hy⟩
    rw [Real.le_sqrt dist_nonneg hnn, dist_comm]; exact hbd_mid y hy
  have hr_le : r ≤ radiusFrom mid Y := circumradius_le_radiusFrom mid Y
  have : r ≤ Real.sqrt (r ^ 2 - (1/4) * dist c₁ c₂ ^ 2) := le_trans hr_le hrf_mid
  rw [Real.le_sqrt hr_nn hnn] at this
  nlinarith [sq_nonneg (dist c₁ c₂)]

/--
[stable_image_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BruhatTitsFixedPoint.lean)
-/
@[path]
lemma stable_image_eq
  [MetricSpace M]
  [Group G]
  {act : IsometricAction G M}
  {Y : Set M}
  {g : G}
-- given
  (hstab : act.IsStable Y) :
-- imply
  act.smul g '' Y = Y := by
-- proof
  ext z; constructor
  · rintro ⟨y, hy, rfl⟩; exact hstab g y hy
  · intro hz
    refine ⟨act.smul g⁻¹ z, hstab g⁻¹ z hz, ?_⟩
    rw [← act.smul_mul, mul_inv_cancel, act.smul_one]

/--
[BruhatTitsFixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BruhatTitsFixedPoint.lean)
-/
@[path]
lemma BruhatTitsFixedPoint
  [MetricSpace M]
  {M : Type*}
  [MetricSpace M]
  [CompleteSpace M]
  {G : Type*}
  [Group G]
  {act : IsometricAction G M}
  {Y : Set M}
-- given
  (hNCI : NegativeCurvatureInequality M)
  (hne : Y.Nonempty)
  (hbd : Bornology.IsBounded Y)
  (hstab : act.IsStable Y) :
-- imply
  ∃ x : M, act.IsFixedPoint x := by
-- proof
  obtain ⟨c, hc⟩ := circumcenter_exists M hNCI Y hne hbd
  refine ⟨c, fun g => ?_⟩
  have hgc : IsCircumcenter (act.smul g c) Y := by
    unfold IsCircumcenter
    calc radiusFrom (act.smul g c) Y
      = radiusFrom (act.smul g c) (act.smul g '' Y) := by
        rw [stable_image_eq act Y hstab g]
      _ = radiusFrom c Y := isometry_radiusFrom_eq (act.smul g) (act.isometry_smul g) c Y
      _ = circumradius Y := hc
  exact (circumcenter_unique M hNCI Y hne hbd c (act.smul g c) hc hgc).symm


-- created on 2026-10-23
