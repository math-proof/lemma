import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Def.Analysis.Calculus.Blumberg.Part4


section

namespace MetaMathlibExt

-- N6: the empty state satisfies the invariant.
theorem blum_inv_empty (f : ℝ → ℝ) : blumInv f (∅, ∅) := by
  unfold blumInv
  simp

-- Removing a meagre set from a non-meagre set leaves a nonempty set.
theorem blum_nonempty_diff_meagre {s B : Set ℝ} (hmeag : IsMeagre B)
    (hnot : ¬ IsMeagre s) : (s \ B).Nonempty := by
  by_contra h
  apply hnot
  have hempty : s \ B = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hsub : s ⊆ (s \ B) ∪ B := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Or.inr hxB
    · exact Or.inl ⟨hx, hxB⟩
  rw [hempty] at hsub
  exact IsMeagre.mono hsub (IsMeagre.union IsMeagre.empty hmeag)

-- Arbitrarily fine dyadic levels.
theorem blum_exists_fine_level (M' : ℕ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ m : ℕ, M' ≤ m ∧ 1 / (2 : ℝ) ^ m < r₀ := by
  have htend : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) Filter.atTop
      (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ((1 : ℝ) / 2) ^ n < r₀ :=
    htend.eventually (Iio_mem_nhds hr₀)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N M', le_max_right _ _, ?_⟩
  have hle : ((1 : ℝ) / 2) ^ (max N M') ≤ ((1 : ℝ) / 2) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left _ _)
  have h12 : ((1 : ℝ) / 2) ^ (max N M') = 1 / (2 : ℝ) ^ (max N M') := by
    rw [div_pow, one_pow]
  rw [← h12]
  exact lt_of_le_of_lt hle (hN _ (le_refl _))

-- N7: add a new point inside a nonempty open set.
theorem blum_add_point (f : ℝ → ℝ) {P : Finset ℝ}
    {L : Finset (ℕ × ℤ × ℝ × ℝ)} (hInv : blumInv f (P, L))
    {U : Set ℝ} (hUo : IsOpen U) (hUne : U.Nonempty) :
    ∃ y : ℝ, y ∈ U ∧ y ∉ (↑P : Set ℝ) ∧ blumInv f (insert y P, L) := by
  classical
  obtain ⟨V1, V2, V3, V4⟩ := hInv
  obtain ⟨y₀, hy₀⟩ := hUne
  obtain ⟨m, hmM, a, hsub, hne⟩ :=
    blum_dyI_small_mem_open hUo hy₀ (L.sup (fun ℓ => ℓ.1) + 1)
  have hlevel : ∀ ℓ : ℕ × ℤ × ℝ × ℝ, ℓ ∈ L → ℓ.1 < m := by
    intro ℓ hℓ
    have hle : ℓ.1 ≤ L.sup (fun ℓ => ℓ.1) := Finset.le_sup hℓ
    omega
  have hVo : IsOpen (blumDyI m a) := by
    rw [blumDyI]
    exact isOpen_Ioo
  set Λ := L.filter
    (fun ℓ => (blumDyI m a ∩ blumDyI ℓ.1 ℓ.2.1).Nonempty) with hΛ
  have hBmeag : IsMeagre
      ({x | ¬ blumGood f x} ∪ blumDyadic ∪ (↑P : Set ℝ)) :=
    IsMeagre.union (IsMeagre.union (blum_isMeagre_not_good f)
      (blum_isMeagre_of_countable _ blum_dyadic_countable))
      (blum_isMeagre_of_countable _ (Finset.finite_toSet P).countable)
  have hVnot : ¬ IsMeagre (blumDyI m a) := not_isMeagre_of_isOpen hVo hne
  have hV1new : ∀ y : ℝ, y ∉
      ({x | ¬ blumGood f x} ∪ blumDyadic ∪ (↑P : Set ℝ)) →
      (blumGood f y ∧ y ∉ blumDyadic) ∧ y ∉ (↑P : Set ℝ) := by
    intro y hyB
    have hyG : blumGood f y := by
      by_contra hG
      exact hyB (Or.inl (Or.inl hG))
    have hyD : y ∉ blumDyadic := by
      intro hD
      exact hyB (Or.inl (Or.inr hD))
    have hyP : y ∉ (↑P : Set ℝ) := by
      intro hP
      exact hyB (Or.inr hP)
    exact ⟨⟨hyG, hyD⟩, hyP⟩
  by_cases hΛempty : Λ = ∅
  · obtain ⟨y, hy⟩ := blum_nonempty_diff_meagre hBmeag hVnot
    obtain ⟨hyV, hyB⟩ : y ∈ blumDyI m a ∧ y ∉
        ({x | ¬ blumGood f x} ∪ blumDyadic ∪ (↑P : Set ℝ)) := hy
    obtain ⟨hyG, hyP⟩ := hV1new y hyB
    refine ⟨y, hsub hyV, hyP, ?_, ?_, V3, V4⟩
    · intro d hd
      have hd' : d = y ∨ d ∈ P := Finset.mem_insert.mp hd
      rcases hd' with rfl | hdP
      · exact hyG
      · exact V1 d hdP
    · intro ℓ hℓ d hd hdy
      have hd' : d = y ∨ d ∈ P := Finset.mem_insert.mp hd
      rcases hd' with rfl | hdP
      · exfalso
        have hmeet : (blumDyI m a ∩ blumDyI ℓ.1 ℓ.2.1).Nonempty :=
          ⟨d, hyV, hdy⟩
        have hmem : ℓ ∈ Λ := Finset.mem_filter.mpr ⟨hℓ, hmeet⟩
        rw [hΛempty] at hmem
        exact Finset.notMem_empty ℓ hmem
      · exact V2 ℓ hℓ d hdP hdy
  · obtain ⟨ℓs, hℓs_mem, hℓs_max⟩ :=
      Finset.exists_max_image Λ (fun ℓ => ℓ.1)
        (Finset.nonempty_iff_ne_empty.mpr hΛempty)
    have hmax : ∀ x' : ℕ × ℤ × ℝ × ℝ, x' ∈ Λ → x'.1 ≤ ℓs.1 :=
      hℓs_max
    have hℓsL : ℓs ∈ L := (Finset.mem_filter.mp hℓs_mem).1
    have hVsub : ∀ ℓ : ℕ × ℤ × ℝ × ℝ, ℓ ∈ Λ →
        blumDyI m a ⊆ blumDyI ℓ.1 ℓ.2.1 := by
      intro ℓ hℓ
      have hℓL : ℓ ∈ L := (Finset.mem_filter.mp hℓ).1
      have hmeet : (blumDyI m a ∩ blumDyI ℓ.1 ℓ.2.1).Nonempty :=
        (Finset.mem_filter.mp hℓ).2
      exact blum_dyI_laminar (le_of_lt (hlevel ℓ hℓL)) hmeet
    have hband : ∀ ℓ : ℕ × ℤ × ℝ × ℝ, ℓ ∈ Λ →
        Metric.ball ℓs.2.2.1 ℓs.2.2.2 ⊆ Metric.ball ℓ.2.2.1 ℓ.2.2.2 := by
      intro ℓ hℓ
      have hℓL : ℓ ∈ L := (Finset.mem_filter.mp hℓ).1
      have h1 : blumDyI m a ⊆ blumDyI ℓs.1 ℓs.2.1 := hVsub ℓs hℓs_mem
      have h2 : blumDyI m a ⊆ blumDyI ℓ.1 ℓ.2.1 := hVsub ℓ hℓ
      have hlev : ℓ.1 ≤ ℓs.1 := hmax ℓ hℓ
      have hne2 : (blumDyI ℓs.1 ℓs.2.1 ∩
          blumDyI ℓ.1 ℓ.2.1).Nonempty := by
        obtain ⟨z, hzm⟩ := hne
        exact ⟨z, h1 hzm, h2 hzm⟩
      exact V3 ℓs hℓsL ℓ hℓL (blum_dyI_laminar hlev hne2)
    have hkey : ¬ IsMeagre ((f ⁻¹' Metric.ball ℓs.2.2.1 ℓs.2.2.2) ∩
        blumDyI m a) :=
      V4 ℓs hℓsL _ hVo hne (hVsub ℓs hℓs_mem)
    obtain ⟨y, hy⟩ := blum_nonempty_diff_meagre hBmeag hkey
    obtain ⟨hyV, hyB⟩ : y ∈ (f ⁻¹' Metric.ball ℓs.2.2.1 ℓs.2.2.2) ∩
        blumDyI m a ∧ y ∉
        ({x | ¬ blumGood f x} ∪ blumDyadic ∪ (↑P : Set ℝ)) := hy
    obtain ⟨hyf, hydy⟩ :
      y ∈ f ⁻¹' Metric.ball ℓs.2.2.1 ℓs.2.2.2 ∧ y ∈ blumDyI m a := hyV
    obtain ⟨hyG, hyP⟩ := hV1new y hyB
    refine ⟨y, hsub hydy, hyP, ?_, ?_, V3, V4⟩
    · intro d hd
      have hd' : d = y ∨ d ∈ P := Finset.mem_insert.mp hd
      rcases hd' with rfl | hdP
      · exact hyG
      · exact V1 d hdP
    · intro ℓ hℓ d hd hdy
      have hd' : d = y ∨ d ∈ P := Finset.mem_insert.mp hd
      rcases hd' with rfl | hdP
      · have hmeet : (blumDyI m a ∩ blumDyI ℓ.1 ℓ.2.1).Nonempty :=
          ⟨d, hydy, hdy⟩
        have hmem : ℓ ∈ Λ := Finset.mem_filter.mpr ⟨hℓ, hmeet⟩
        have hfy : f d ∈ Metric.ball ℓs.2.2.1 ℓs.2.2.2 := hyf
        exact Metric.mem_ball.mp ((hband ℓ hmem) hfy)
      · exact V2 ℓ hℓ d hdP hdy

-- N8: add a fine label around an existing point.
theorem blum_add_label (f : ℝ → ℝ) {P : Finset ℝ}
    {L : Finset (ℕ × ℤ × ℝ × ℝ)} (hInv : blumInv f (P, L))
    {d : ℝ} (hdP : d ∈ P) (k : ℕ) :
    ∃ ℓ : ℕ × ℤ × ℝ × ℝ, d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((k : ℝ) + 1) ∧
      blumInv f (P, insert ℓ L) := by
  classical
  obtain ⟨V1, V2, V3, V4⟩ := hInv
  obtain ⟨hdGood, hdDy⟩ := V1 d hdP
  have hK : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hKinv : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  set S := L.filter (fun ℓ => d ∈ blumDyI ℓ.1 ℓ.2.1) with hS
  obtain ⟨ε, hεpos, hεK, hεsub⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / ((k : ℝ) + 1) ∧
      ∀ ℓ ∈ S, Metric.ball (f d) ε ⊆ Metric.ball ℓ.2.2.1 ℓ.2.2.2 := by
    by_cases hSe : S = ∅
    · refine ⟨1 / ((k : ℝ) + 1), hKinv, le_rfl, ?_⟩
      intro ℓ hℓ
      rw [hSe] at hℓ
      exact absurd hℓ (Finset.notMem_empty ℓ)
    · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSe
      set T := S.image (fun ℓ => ℓ.2.2.2 - dist (f d) ℓ.2.2.1) with hT
      have hTne : T.Nonempty := hSne.image _
      have hmem2 : ∀ ℓ ∈ S, dist (f d) ℓ.2.2.1 < ℓ.2.2.2 := by
        intro ℓ hℓ
        have hL : ℓ ∈ L := (Finset.mem_filter.mp hℓ).1
        have hdy : d ∈ blumDyI ℓ.1 ℓ.2.1 := (Finset.mem_filter.mp hℓ).2
        exact V2 ℓ hL d hdP hdy
      have hTpos : ∀ t ∈ T, 0 < t := by
        intro t ht
        obtain ⟨ℓ, hℓS, hfa⟩ := Finset.mem_image.mp ht
        have hfa' : ℓ.2.2.2 - dist (f d) ℓ.2.2.1 = t := hfa
        rw [← hfa']
        linarith [hmem2 ℓ hℓS]
      have hminpos : 0 < T.min' hTne := hTpos _ (Finset.min'_mem _ hTne)
      refine ⟨min (1 / ((k : ℝ) + 1)) (T.min' hTne),
        lt_min hKinv hminpos, min_le_left _ _, ?_⟩
      intro ℓ hℓ
      have hle : min (1 / ((k : ℝ) + 1)) (T.min' hTne) ≤
          ℓ.2.2.2 - dist (f d) ℓ.2.2.1 :=
        le_trans (min_le_right _ _)
          (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩))
      intro y hy
      rw [Metric.mem_ball] at hy ⊢
      have htri : dist y ℓ.2.2.1 ≤ dist y (f d) + dist (f d) ℓ.2.2.1 :=
        dist_triangle _ _ _
      linarith
  obtain ⟨ρ, hρ, hGoodρ⟩ := hdGood ε hεpos
  obtain ⟨g, hgpos, hgρ, hgisol⟩ : ∃ g : ℝ, 0 < g ∧ g ≤ ρ ∧
      ∀ d' ∈ P, d' ≠ d → g ≤ dist d d' := by
    set E := P.erase d with hE
    by_cases hEe : E = ∅
    · refine ⟨ρ, hρ, le_rfl, ?_⟩
      intro d' hd' hne
      have hmem : d' ∈ E := Finset.mem_erase.mpr ⟨hne, hd'⟩
      rw [hEe] at hmem
      exact absurd hmem (Finset.notMem_empty d')
    · have hEne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEe
      set Dists := E.image (fun d' => dist d d') with hD
      have hDne : Dists.Nonempty := hEne.image _
      have hDpos : ∀ t ∈ Dists, 0 < t := by
        intro t ht
        obtain ⟨d', hd'E, hfa⟩ := Finset.mem_image.mp ht
        have hne : d' ≠ d := (Finset.mem_erase.mp hd'E).1
        have hfa' : dist d d' = t := hfa
        rw [← hfa']
        exact dist_pos.mpr (Ne.symm hne)
      have hminpos : 0 < Dists.min' hDne := hDpos _ (Finset.min'_mem _ hDne)
      refine ⟨min ρ (Dists.min' hDne), lt_min hρ hminpos, min_le_left _ _, ?_⟩
      intro d' hd' hne
      have hmem : d' ∈ E := Finset.mem_erase.mpr ⟨hne, hd'⟩
      exact le_trans (min_le_right _ _)
        (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨d', hmem, rfl⟩))
  obtain ⟨m, hmM, hmlt⟩ :=
    blum_exists_fine_level (L.sup (fun ℓ => ℓ.1) + 1) hgpos
  have hlevel : ∀ ℓ ∈ L, ℓ.1 < m := by
    intro ℓ hℓ
    have hle : ℓ.1 ≤ L.sup (fun ℓ => ℓ.1) := Finset.le_sup hℓ
    omega
  have hdmem : d ∈ blumDyI m ⌊d * 2 ^ m⌋ := blum_mem_dyI_floor m hdDy
  have hball : blumDyI m ⌊d * 2 ^ m⌋ ⊆ Metric.ball d (1 / 2 ^ m) :=
    blum_dyI_subset_ball m _ hdmem
  have hisol : ∀ d' ∈ P, d' ∈ blumDyI m ⌊d * 2 ^ m⌋ → d' = d := by
    intro d' hd'P hd'I
    by_contra hne
    have h1 : dist d' d < 1 / 2 ^ m := Metric.mem_ball.mp (hball hd'I)
    have h2 : g ≤ dist d d' := hgisol d' hd'P hne
    rw [dist_comm d d'] at h2
    linarith
  refine ⟨(m, ⌊d * 2 ^ m⌋, f d, ε), hdmem, hεK, ?_, ?_, ?_, ?_⟩
  · exact V1
  · intro q hq d' hd'P hd'I
    rcases Finset.mem_insert.mp hq with rfl | hqL
    · have hdd : d' = d := hisol d' hd'P hd'I
      rw [hdd]
      change dist (f d) (f d) < ε
      rw [dist_self]
      exact hεpos
    · exact V2 q hqL d' hd'P hd'I
  · intro q hq q' hq' hsub
    rcases Finset.mem_insert.mp hq with rfl | hqL
    · rcases Finset.mem_insert.mp hq' with rfl | hq'L
      · exact le_rfl
      · exact hεsub q' (Finset.mem_filter.mpr ⟨hq'L, hsub hdmem⟩)
    · rcases Finset.mem_insert.mp hq' with rfl | hq'L
      · exact absurd hsub (blum_dyI_not_subset_of_lt (hlevel q hqL))
      · exact V3 q hqL q' hq'L hsub
  · intro q hq V hVo hVne hVsub
    rcases Finset.mem_insert.mp hq with rfl | hqL
    · have hle : (1 : ℝ) / 2 ^ m ≤ ρ := le_trans (le_of_lt hmlt) hgρ
      have hVsub' : V ⊆ Metric.ball d ρ :=
        hVsub.trans (hball.trans (Metric.ball_subset_ball hle))
      have hkey := hGoodρ V hVo hVne hVsub'
      change ¬ IsMeagre ((f ⁻¹' Metric.ball (f d) ε) ∩ V)
      have heq : (f ⁻¹' Metric.ball (f d) ε) = {y | dist (f y) (f d) < ε} := by
        ext y
        simp [Metric.mem_ball]
      rw [heq]
      exact hkey
    · exact V4 q hqL V hVo hVne hVsub

-- N9: one full stage: add a point in U (if open nonempty) and fine labels everywhere.
theorem blum_step (f : ℝ → ℝ) {P : Finset ℝ} {L : Finset (ℕ × ℤ × ℝ × ℝ)}
    (hInv : blumInv f (P, L)) (U : Set ℝ) (k : ℕ) :
    ∃ P' : Finset ℝ, ∃ L' : Finset (ℕ × ℤ × ℝ × ℝ), P ⊆ P' ∧ L ⊆ L' ∧
      blumInv f (P', L') ∧ (U.Nonempty → IsOpen U → (↑P' ∩ U).Nonempty) ∧
      ∀ d ∈ P, ∃ ℓ ∈ L', d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((k : ℝ) + 1) := by
  classical
  obtain ⟨P1, hPsub, hInv1, hUmeet⟩ :
      ∃ P1 : Finset ℝ, P ⊆ P1 ∧ blumInv f (P1, L) ∧
        (U.Nonempty → IsOpen U → (↑P1 ∩ U).Nonempty) := by
    by_cases hU : U.Nonempty ∧ IsOpen U
    · obtain ⟨hUne, hUo⟩ := hU
      obtain ⟨y, hyU, _, hInv1⟩ := blum_add_point f hInv hUo hUne
      refine ⟨insert y P, Finset.subset_insert y P, hInv1, ?_⟩
      intro _ _
      exact ⟨y, Finset.mem_coe.mpr (Finset.mem_insert_self y P), hyU⟩
    · refine ⟨P, (fun x hx => hx), hInv, ?_⟩
      intro hUne hUo
      exact absurd ⟨hUne, hUo⟩ hU
  have key : ∀ S : Finset ℝ, S ⊆ P1 →
      ∀ L₀ : Finset (ℕ × ℤ × ℝ × ℝ), L ⊆ L₀ → blumInv f (P1, L₀) →
      ∃ L', L₀ ⊆ L' ∧ blumInv f (P1, L') ∧
        ∀ d ∈ S, ∃ ℓ ∈ L', d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((k : ℝ) + 1) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro _ L₀ hLL₀ hInv₀
      exact ⟨L₀, (fun x hx => hx), hInv₀,
        fun d hd => absurd hd (Finset.notMem_empty d)⟩
    · intro a S' haS' IH hsub L₀ hLL₀ hInv₀
      have haP1 : a ∈ P1 := hsub (Finset.mem_insert_self a S')
      have hS'P1 : S' ⊆ P1 := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      obtain ⟨L₁, hL₀₁, hInv₁, hlab₁⟩ := IH hS'P1 L₀ hLL₀ hInv₀
      obtain ⟨ℓn, hmem_n, hr_n, hInv₂⟩ := blum_add_label f hInv₁ haP1 k
      refine ⟨insert ℓn L₁, fun x hx => Finset.mem_insert_of_mem (hL₀₁ hx),
        hInv₂, ?_⟩
      intro d hd
      rcases Finset.mem_insert.mp hd with hda | hdS'
      · refine ⟨ℓn, Finset.mem_insert_self ℓn L₁, ?_, hr_n⟩
        rw [hda]
        exact hmem_n
      · obtain ⟨ℓ, hℓ, hdy, hr⟩ := hlab₁ d hdS'
        exact ⟨ℓ, Finset.mem_insert_of_mem hℓ, hdy, hr⟩
  obtain ⟨L', hLL', hInv', hlab'⟩ :=
    key P1 (fun x hx => hx) L (fun x hx => hx) hInv1
  refine ⟨P1, L', hPsub, hLL', hInv', hUmeet, ?_⟩
  intro d hd
  obtain ⟨ℓ, hℓ, hdy, hr⟩ := hlab' d (hPsub hd)
  exact ⟨ℓ, hℓ, hdy, hr⟩

-- N10: the stage sequence.
theorem blum_seq (f : ℝ → ℝ) :
    ∃ σ : ℕ → ℚ × ℚ, Function.Surjective σ ∧
    ∃ s : ℕ → Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ),
      s 0 = (∅, ∅) ∧ (∀ n, blumInv f (s n)) ∧
      (∀ n n' : ℕ, n ≤ n' → (s n).1 ⊆ (s n').1) ∧
      (∀ n n' : ℕ, n ≤ n' → (s n).2 ⊆ (s n').2) ∧
      (∀ n, (Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty →
        (↑(s (n+1)).1 ∩ Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty) ∧
      (∀ n, ∀ d ∈ (s n).1, ∃ ℓ ∈ (s (n+1)).2,
        d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((n : ℝ) + 1)) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_surjective_nat (ℚ × ℚ)
  have hstep : ∀ st : Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ), blumInv f st →
      ∀ n : ℕ, ∃ st' : Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ),
        st.1 ⊆ st'.1 ∧ st.2 ⊆ st'.2 ∧ blumInv f st' ∧
        ((Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty →
          (↑st'.1 ∩ Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty) ∧
        ∀ d ∈ st.1, ∃ ℓ ∈ st'.2,
          d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((n : ℝ) + 1) := by
    intro st hst n
    obtain ⟨P', L', hPP', hLL', hInv', hmeet, hlab⟩ :=
      blum_step f hst (Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)) n
    exact ⟨(P', L'), hPP', hLL', hInv', fun hne => hmeet hne isOpen_Ioo,
      fun d hd => hlab d hd⟩
  have hstep' : ∀ st : {st : Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ) // blumInv f st},
      ∀ n : ℕ, ∃ st' : {st : Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ) // blumInv f st},
        st.val.1 ⊆ st'.val.1 ∧ st.val.2 ⊆ st'.val.2 ∧
        ((Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty →
          (↑st'.val.1 ∩ Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty) ∧
        ∀ d ∈ st.val.1, ∃ ℓ ∈ st'.val.2,
          d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((n : ℝ) + 1) := by
    intro st n
    obtain ⟨⟨P', L'⟩, hPP', hLL', hInv', hmeet, hlab⟩ :=
      hstep st.val st.property n
    exact ⟨⟨(P', L'), hInv'⟩, hPP', hLL', hmeet, fun d hd => hlab d hd⟩
  choose nxt hnxt using hstep'
  obtain ⟨s, hs0, hsS⟩ : ∃ s : ℕ →
      {st : Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ) // blumInv f st},
      s 0 = ⟨(∅, ∅), blum_inv_empty f⟩ ∧ ∀ n, s (n + 1) = nxt (s n) n :=
    ⟨fun n => Nat.rec (motive := fun _ => _) ⟨(∅, ∅), blum_inv_empty f⟩
      (fun n st => nxt st n) n, rfl, fun n => rfl⟩
  have hmonoP : ∀ n n' : ℕ, n ≤ n' → (s n).val.1 ⊆ (s n').val.1 := by
    intro n n'
    induction n' with
    | zero =>
      intro h
      have hn0 : n = 0 := Nat.le_zero.mp h
      rw [hn0]
    | succ k IH =>
      intro h
      by_cases hkn : n ≤ k
      · intro x hx
        have h1 : x ∈ (s k).val.1 := IH hkn hx
        have h2 := (hnxt (s k) k).1
        rw [← hsS k] at h2
        exact h2 h1
      · have hnk : n = k + 1 := by omega
        rw [hnk]
  have hmonoL : ∀ n n' : ℕ, n ≤ n' → (s n).val.2 ⊆ (s n').val.2 := by
    intro n n'
    induction n' with
    | zero =>
      intro h
      have hn0 : n = 0 := Nat.le_zero.mp h
      rw [hn0]
    | succ k IH =>
      intro h
      by_cases hkn : n ≤ k
      · intro x hx
        have h1 : x ∈ (s k).val.2 := IH hkn hx
        have h2 := (hnxt (s k) k).2.1
        rw [← hsS k] at h2
        exact h2 h1
      · have hnk : n = k + 1 := by omega
        rw [hnk]
  refine ⟨σ, hσ, fun n => (s n).val, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (s 0).val = (∅, ∅)
    rw [hs0]
  · intro n
    exact (s n).property
  · intro n n' hnn'
    exact hmonoP n n' hnn'
  · intro n n' hnn'
    exact hmonoL n n' hnn'
  · intro n hne
    change (↑(s (n+1)).val.1 ∩ Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty
    rw [hsS n]
    exact (hnxt (s n) n).2.2.1 hne
  · intro n d hd
    change ∃ ℓ ∈ (s (n+1)).val.2, d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((n : ℝ) + 1)
    obtain ⟨ℓ, hℓ, hdy, hr⟩ := (hnxt (s n) n).2.2.2 d hd
    rw [← hsS n] at hℓ
    exact ⟨ℓ, hℓ, hdy, hr⟩

-- N11: density and continuity from the stage sequence.
theorem blum_dense_cont (f : ℝ → ℝ) (σ : ℕ → ℚ × ℚ)
    (hσ : Function.Surjective σ)
    (s : ℕ → Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ))
    (hsInv : ∀ n, blumInv f (s n))
    (hmonoP : ∀ n n' : ℕ, n ≤ n' → (s n).1 ⊆ (s n').1)
    (hmonoL : ∀ n n' : ℕ, n ≤ n' → (s n).2 ⊆ (s n').2)
    (hmeet : ∀ n, (Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty →
      (↑(s (n+1)).1 ∩ Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty)
    (hlab : ∀ n, ∀ d ∈ (s n).1, ∃ ℓ ∈ (s (n+1)).2,
      d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((n : ℝ) + 1)) :
    ∃ D : Set ℝ, Dense D ∧ ContinuousOn f D := by
  classical
  set D : Set ℝ := ⋃ n, ↑(s n).1 with hD
  have hDmem : ∀ n, ∀ d : ℝ, d ∈ (s n).1 → d ∈ D := by
    intro n d hd
    rw [hD]
    exact Set.mem_iUnion.mpr ⟨n, Finset.mem_coe.mpr hd⟩
  refine ⟨D, ?_, ?_⟩
  · rw [dense_iff_inter_open]
    intro W hWo hWne
    obtain ⟨y, hyW⟩ := hWne
    obtain ⟨r, hrpos, hrsub⟩ := Metric.isOpen_iff.mp hWo y hyW
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show y - r / 2 < y by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (y : ℝ) < y + r / 2 by linarith)
    have hIooW : Set.Ioo ((p : ℚ) : ℝ) ((q : ℚ) : ℝ) ⊆ W := by
      intro z hz
      apply hrsub
      have hz' : ((p : ℚ) : ℝ) < z ∧ z < ((q : ℚ) : ℝ) := hz
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hz'.1, hz'.2, hp1, hp2, hq1, hq2, hrpos]
    have hIne : (Set.Ioo ((p : ℚ) : ℝ) ((q : ℚ) : ℝ)).Nonempty :=
      ⟨y, hp2, hq1⟩
    obtain ⟨n, hn⟩ := hσ (p, q)
    have hp_eq : ((σ n).1 : ℝ) = ((p : ℚ) : ℝ) := by rw [hn]
    have hq_eq : ((σ n).2 : ℝ) = ((q : ℚ) : ℝ) := by rw [hn]
    have hne : (Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty := by
      rw [hp_eq, hq_eq]
      exact hIne
    obtain ⟨z, hzmem, hzIoo⟩ := hmeet n hne
    rw [hp_eq, hq_eq] at hzIoo
    exact ⟨z, hIooW hzIoo, hDmem (n + 1) z hzmem⟩
  · rw [Metric.continuousOn_iff]
    intro d hdD ε hεpos
    have hdD' : d ∈ ⋃ m, ↑(s m).1 := by rw [← hD]; exact hdD
    obtain ⟨n₀, hn₀'⟩ := Set.mem_iUnion.mp hdD'
    have hn₀ : d ∈ (s n₀).1 := Finset.mem_coe.mp hn₀'
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε / 2 by linarith)
    set n := max k n₀ with hn
    have hn0 : n₀ ≤ n := le_max_right _ _
    have hnk : k ≤ n := le_max_left _ _
    have hdP : d ∈ (s n).1 := hmonoP n₀ n hn0 hn₀
    obtain ⟨ℓ, hℓL, hdy, hr⟩ := hlab n d hdP
    have h2 : 2 * (1 / ((n : ℝ) + 1)) < ε := by
      have hkk : ((k : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
        exact_mod_cast Nat.succ_le_succ hnk
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hkk
      linarith [hk]
    have hopen : IsOpen (blumDyI ℓ.1 ℓ.2.1) := by
      rw [blumDyI]
      exact isOpen_Ioo
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hopen d hdy
    refine ⟨δ, hδpos, ?_⟩
    intro y hyD hydist
    have hyD'' : y ∈ ⋃ m, ↑(s m).1 := by rw [← hD]; exact hyD
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hyD''
    have hyP : y ∈ (s N).1 := Finset.mem_coe.mp hN
    set N' := max N (n + 1) with hN'
    have hNN' : N ≤ N' := le_max_left _ _
    have hnN' : n + 1 ≤ N' := le_max_right _ _
    have hyP' : y ∈ (s N').1 := hmonoP N N' hNN' hyP
    have hdP' : d ∈ (s N').1 := hmonoP n N' (le_trans (Nat.le_succ n) hnN') hdP
    have hℓL' : ℓ ∈ (s N').2 := hmonoL (n + 1) N' hnN' hℓL
    obtain ⟨oV1, oV2, oV3, oV4⟩ := hsInv N'
    have hymem : y ∈ blumDyI ℓ.1 ℓ.2.1 :=
      hδsub (Metric.mem_ball.mpr hydist)
    have hfy : dist (f y) ℓ.2.2.1 < ℓ.2.2.2 := oV2 ℓ hℓL' y hyP' hymem
    have hfd : dist (f d) ℓ.2.2.1 < ℓ.2.2.2 := oV2 ℓ hℓL' d hdP' hdy
    have htri : dist (f y) (f d) ≤ dist (f y) ℓ.2.2.1 + dist (f d) ℓ.2.2.1 := by
      have h := dist_triangle (f y) ℓ.2.2.1 (f d)
      rwa [dist_comm ℓ.2.2.1 (f d)] at h
    linarith [htri, hfy, hfd, hr, h2]

/-- Blumberg's theorem (https://en.wikipedia.org/wiki/Blumberg_theorem, statement blumberg-s1):
every function `f : ℝ → ℝ` is continuous on some dense set.

Proves `Wanted` entry `blumberg_theorem`.
-/
theorem blumberg_theorem : ∀ f : ℝ → ℝ, ∃ D : Set ℝ, Dense D ∧ ContinuousOn f D := by
  intro f
  obtain ⟨σ, hσ, s, hs0, hsInv, hmonoP, hmonoL, hmeet, hlab⟩ := blum_seq f
  exact blum_dense_cont f σ hσ s hsInv hmonoP hmonoL hmeet hlab

end MetaMathlibExt
end
