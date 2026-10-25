import Mathlib
import sympy.Basic
import Def.v1.Atlas.TheoryOfProbability.code.HellySelection
open Filter Set Function
open scoped Topology


/--
[IsDistributionFunction.nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/HellySelection.lean)
-/
@[path]
lemma IsDistributionFunction.nonneg
  {F : ℝ → ℝ}
  {x : ℝ}
-- given
  (hF : IsDistributionFunction F) :
-- imply
  0 ≤ F x :=
-- proof
  le_of_tendsto hF.tendsto_atBot (eventually_atBot.mpr ⟨x, fun _ hy => hF.mono hy⟩)

/--
[IsDistributionFunction.le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/HellySelection.lean)
-/
@[path]
lemma IsDistributionFunction.le_one
  {F : ℝ → ℝ}
  {x : ℝ}
-- given
  (hF : IsDistributionFunction F) :
-- imply
  F x ≤ 1 :=
-- proof
  ge_of_tendsto hF.tendsto_atTop (eventually_atTop.mpr ⟨x, fun _ hy => hF.mono hy⟩)

/--
[IsDistributionFunction.mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/HellySelection.lean)
-/
@[path]
lemma IsDistributionFunction.mem_Icc
  {F : ℝ → ℝ}
  {x : ℝ}
-- given
  (hF : IsDistributionFunction F) :
-- imply
  F x ∈ Icc (0 : ℝ) 1 :=
-- proof
  ⟨hF.nonneg x, hF.le_one x⟩
namespace HellySelection

/--
[sSup_image_rat_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/HellySelection.lean)
-/
@[path]
lemma sSup_image_rat_eq
  {g : ℚ → ℝ}
  {q : ℚ}
-- given
  (hg_mono : ∀ q₁ q₂ : ℚ, q₁ ≤ q₂ → g q₁ ≤ g q₂)
  (hg_bdd : ∀ q, 0 ≤ g q ∧ g q ≤ 1) :
-- imply
  sSup (g '' { r : ℚ | (r : ℝ) ≤ ↑q }) = g q := by
-- proof
  apply le_antisymm
  · apply csSup_le
    · exact ⟨g q, ⟨q, show (q : ℝ) ≤ ↑q from le_rfl, rfl⟩⟩
    · rintro _ ⟨r, (hr : (r : ℝ) ≤ ↑q), rfl⟩
      exact hg_mono r q (Rat.cast_le.mp hr)
  · exact le_csSup ⟨1, by rintro _ ⟨r, _, rfl⟩; exact (hg_bdd r).2⟩
    ⟨q, show (q : ℝ) ≤ ↑q from le_rfl, rfl⟩

/--
[helly_selection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/HellySelection.lean)
-/
@[path]
lemma helly_selection
  {F : ℕ → ℝ → ℝ}
-- given
  (hF : ∀ n, IsDistributionFunction (F n)) :
-- imply
  ∃ (φ : ℕ → ℕ) (G : HellySelection.MonotoneRightContinuous), StrictMono φ ∧ ∀ x, ContinuousAt (↑G) x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x)) := by
-- proof
  classical
  let v : ℕ → ℚ → Set.Icc (0 : ℝ) 1 :=
    fun n q => ⟨F n ↑q, (hF n).nonneg ↑q, (hF n).le_one ↑q⟩
  obtain ⟨a, φ, hφ_strict, hφ_conv⟩ := CompactSpace.tendsto_subseq v
  have hconv_rat : ∀ q : ℚ, Tendsto (fun k => F (φ k) (↑q)) atTop (𝓝 ↑(a q)) := by
    intro q
    have h1 : Tendsto (fun k => (v ∘ φ) k q) atTop (𝓝 (a q)) := tendsto_pi_nhds.mp hφ_conv q
    exact (continuous_subtype_val.tendsto _).comp h1
  let g : ℚ → ℝ := fun q => ↑(a q)
  have hg_mono : ∀ q₁ q₂ : ℚ, q₁ ≤ q₂ → g q₁ ≤ g q₂ := by
    intro p q hpq
    exact le_of_tendsto_of_tendsto (hconv_rat p) (hconv_rat q)
      (Eventually.of_forall fun k => (hF (φ k)).mono (Rat.cast_le.mpr hpq))
  have hg_bdd : ∀ q, 0 ≤ g q ∧ g q ≤ 1 := fun q => (a q).2
  let h : ℝ → ℝ := fun x => sSup (g '' { q : ℚ | (q : ℝ) ≤ x })
  have hh_mono : Monotone h := by
    intro a b hab
    simp only [h]
    apply csSup_le_csSup
    · exact ⟨1, by rintro _ ⟨q, _, rfl⟩; exact (hg_bdd q).2⟩
    · obtain ⟨q, hq⟩ := exists_rat_lt a
      exact ⟨g q, ⟨q, le_of_lt hq, rfl⟩⟩
    · exact image_mono (fun q (hq : (q : ℝ) ≤ a) => le_trans hq hab)
  have hh_rat : ∀ q : ℚ, h (↑q) = g q := sSup_image_rat_eq g hg_mono hg_bdd
  let G := HellySelection.ofMonotone h hh_mono
  refine ⟨φ, G, hφ_strict, ?_⟩
  intro x hx_cont
  have hleft_eq : leftLim h x = rightLim h x := by
    have hlr := hh_mono.rightLim.continuousAt_iff_leftLim_eq_rightLim.mp hx_cont
    rw [leftLim_rightLim (hh_mono.tendsto_leftLim x)] at hlr
    rwa [rightLim_rightLim (hh_mono.tendsto_rightLim x)] at hlr
  have htend_left : Tendsto h (𝓝[<] x) (𝓝 (G x)) := by
    show Tendsto h (𝓝[<] x) (𝓝 (rightLim h x))
    rw [← hleft_eq]; exact hh_mono.tendsto_leftLim x
  have htend_right : Tendsto h (𝓝[>] x) (𝓝 (G x)) :=
    hh_mono.tendsto_rightLim x
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  obtain ⟨r, hr_lt, hr_close⟩ : ∃ r : ℚ, (r : ℝ) < x ∧ G x - ε / 2 < h r := by
    have hev : ∀ᶠ y in 𝓝[<] x, dist (h y) (G x) < ε / 2 :=
      (Metric.tendsto_nhds.mp htend_left) (ε / 2) hε2
    rw [Filter.Eventually, mem_nhdsWithin] at hev
    obtain ⟨U, hU_open, hxU, hU_sub⟩ := hev
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hU_open x hxU
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (sub_lt_self x hδ_pos)
    refine ⟨r, hr2, ?_⟩
    have hr_mem : (r : ℝ) ∈ U ∩ Iio x :=
      ⟨hδ_sub (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith), hr2⟩
    have : dist (h ↑r) (G x) < ε / 2 := hU_sub hr_mem
    rw [Real.dist_eq, abs_lt] at this; linarith [this.1]
  obtain ⟨s, hs_lt, hs_close⟩ : ∃ s : ℚ, x < (s : ℝ) ∧ h s < G x + ε / 2 := by
    have hev : ∀ᶠ y in 𝓝[>] x, dist (h y) (G x) < ε / 2 :=
      (Metric.tendsto_nhds.mp htend_right) (ε / 2) hε2
    rw [Filter.Eventually, mem_nhdsWithin] at hev
    obtain ⟨V, hV_open, hxV, hV_sub⟩ := hev
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hV_open x hxV
    obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show x < x + δ by linarith)
    refine ⟨s, hs1, ?_⟩
    have hs_mem : (s : ℝ) ∈ V ∩ Ioi x :=
      ⟨hδ_sub (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith), hs1⟩
    have : dist (h ↑s) (G x) < ε / 2 := hV_sub hs_mem
    rw [Real.dist_eq, abs_lt] at this; linarith [this.2]
  rw [hh_rat] at hr_close hs_close
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp (hconv_rat r)) (ε / 2) hε2
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp (hconv_rat s)) (ε / 2) hε2
  refine ⟨max N₁ N₂, fun k hk => ?_⟩
  have hFr := hN₁ k (le_of_max_le_left hk)
  have hFs := hN₂ k (le_of_max_le_right hk)
  rw [Real.dist_eq, abs_lt] at hFr hFs
  have hle_r : F (φ k) ↑r ≤ F (φ k) x := (hF (φ k)).mono (le_of_lt hr_lt)
  have hle_s : F (φ k) x ≤ F (φ k) ↑s := (hF (φ k)).mono (le_of_lt hs_lt)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith


-- created on 2026-10-23
