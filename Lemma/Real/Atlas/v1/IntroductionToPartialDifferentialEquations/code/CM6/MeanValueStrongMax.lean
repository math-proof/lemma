import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM6.MeanValueStrongMax
open Set Metric MeasureTheory CM6


namespace CM6

/--
[harmonic_volume_mean_value](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM6/MeanValueStrongMax.lean)
-/
@[path]
lemma harmonic_volume_mean_value
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
  {u : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}
  {R : ℝ}
-- given
  (hn : 0 < n)
  (hu : CM7.IsHarmonic u Ω)
  (hR : 0 < R)
  (hball : Metric.closedBall x R ⊆ Ω) :
-- imply
  u x = ⨍ y in Metric.ball x R, u y :=
-- proof
  CM7.harmonic_volume_mean_value hn hu hR hball

end CM6

namespace CM6

/--
[harmonic_sphere_mean_value](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM6/MeanValueStrongMax.lean)
-/
@[path]
lemma harmonic_sphere_mean_value
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
  {u : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}
  {R : ℝ}
-- given
  (hn : 0 < n)
  (hu : CM7.IsHarmonic u Ω)
  (hR : 0 < R)
  (hball : Metric.closedBall x R ⊆ Ω) :
-- imply
  u x = ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1, u (x + R • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ) := by
-- proof
  have hu_ball : CM7.IsHarmonic u (Metric.ball x R) :=
    ⟨hu.contDiffOn.mono (Metric.ball_subset_closedBall.trans hball),
      fun y hy => hu.laplacian_eq_zero y (hball (Metric.ball_subset_closedBall hy))⟩
  have key := CM7.harmonic_sphere_mean_value hn u x R hR hu_ball R hR le_rfl
  rwa [CM7.sphericalMean, if_neg (ne_of_gt hR)] at key

end CM6

namespace CM6

/--
[mean_value_property](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM6/MeanValueStrongMax.lean)
-/
@[path]
lemma mean_value_property
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
  {u : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}
  {R : ℝ}
-- given
  (hn : 0 < n)
  (hu : CM7.IsHarmonic u Ω)
  (hR : 0 < R)
  (hball : Metric.closedBall x R ⊆ Ω) :
-- imply
  (u x = ⨍ y in Metric.ball x R, u y) ∧ (u x = ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1, u (x + R • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) :=
-- proof
  ⟨harmonic_volume_mean_value hn hu hR hball,
    harmonic_sphere_mean_value hn hu hR hball⟩

end CM6

namespace CM6

/--
[strong_maximum_principle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM6/MeanValueStrongMax.lean)
-/
@[path]
lemma strong_maximum_principle
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
  {u : (Fin n → ℝ) → ℝ}
  {p : Fin n → ℝ}
-- given
  (hΩo : IsOpen Ω)
  (hΩc : IsConnected Ω)
  (hmvp : CM7.HasVolumeMVP u Ω)
  (hp : p ∈ Ω)
  (hmax : ∀ x ∈ Ω, u x ≤ u p) :
-- imply
  ∀ x ∈ Ω, u x = u p :=
-- proof
  CM7.strong_max_principle hΩo hΩc hmvp hp hmax

end CM6

namespace CM6

/--
[strong_minimum_principle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM6/MeanValueStrongMax.lean)
-/
@[path]
lemma strong_minimum_principle
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
  {u : (Fin n → ℝ) → ℝ}
  {p : Fin n → ℝ}
-- given
  (hΩo : IsOpen Ω)
  (hΩc : IsConnected Ω)
  (hmvp : CM7.HasVolumeMVP u Ω)
  (hp : p ∈ Ω)
  (hmin : ∀ x ∈ Ω, u p ≤ u x) :
-- imply
  ∀ x ∈ Ω, u x = u p :=
-- proof
  CM7.strong_min_principle hΩo hΩc hmvp hp hmin

end CM6

namespace CM6

/--
[strong_max_principle_combined](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM6/MeanValueStrongMax.lean)
-/
@[path]
lemma strong_max_principle_combined
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
  {u : (Fin n → ℝ) → ℝ}
  {p : Fin n → ℝ}
-- given
  (hΩo : IsOpen Ω)
  (hΩc : IsConnected Ω)
  (hmvp : CM7.HasVolumeMVP u Ω)
  (hp : p ∈ Ω)
  (hextreme : (∀ x ∈ Ω, u x ≤ u p) ∨ (∀ x ∈ Ω, u p ≤ u x)) :
-- imply
  ∀ x ∈ Ω, u x = u p := by
-- proof
  obtain hmax | hmin := hextreme
  · exact strong_maximum_principle hΩo hΩc hmvp hp hmax
  · exact strong_minimum_principle hΩo hΩc hmvp hp hmin

end CM6

namespace CM6

/--
[strong_max_principle_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM6/MeanValueStrongMax.lean)
-/
@[path]
lemma strong_max_principle_bounded
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
  {u : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}
-- given
  (hΩo : IsOpen Ω)
  (hΩc : IsConnected Ω)
  (hΩb : Bornology.IsBounded Ω)
  (hmvp : CM7.HasVolumeMVP u Ω)
  (huc : ContinuousOn u (closure Ω))
  (hnc : ¬ ∀ x ∈ Ω, ∀ y ∈ Ω, u x = u y)
  (hx : x ∈ Ω) :
-- imply
  (∃ q ∈ frontier Ω, u x < u q) ∧ (∃ q ∈ frontier Ω, u q < u x) := by
-- proof
  have hcompact : IsCompact (closure Ω) := hΩb.isCompact_closure
  have hne_closure : (closure Ω).Nonempty := ⟨x, subset_closure hx⟩
  have hnot_const_at : ¬ ∀ y ∈ Ω, u y = u x := by
    intro hall; exact hnc (fun a ha b hb => by rw [hall a ha, hall b hb])
  constructor
  ·
    obtain ⟨p, hp_mem, hp_max⟩ := hcompact.exists_isMaxOn hne_closure huc
    by_cases hp_in : p ∈ Ω
    ·
      exfalso
      have hmax_Ω : ∀ y ∈ Ω, u y ≤ u p := fun y hy => hp_max (subset_closure hy)
      have := CM7.strong_max_principle hΩo hΩc hmvp hp_in hmax_Ω
      exact hnot_const_at (fun y hy => (this y hy).trans (this x hx).symm)
    ·
      have hp_frontier : p ∈ frontier Ω := by
        rw [frontier_eq_closure_inter_closure, Set.mem_inter_iff]
        exact ⟨hp_mem, by rwa [hΩo.isClosed_compl.closure_eq, Set.mem_compl_iff]⟩
      refine ⟨p, hp_frontier, ?_⟩
      have hle : u x ≤ u p := hp_max (subset_closure hx)
      obtain hlt | heq := lt_or_eq_of_le hle
      · exact hlt
      · exfalso
        have hmax_Ω : ∀ y ∈ Ω, u y ≤ u x := fun y hy =>
          heq ▸ hp_max (subset_closure hy)
        have := CM7.strong_max_principle hΩo hΩc hmvp hx hmax_Ω
        exact hnot_const_at (fun y hy => (this y hy).trans (this x hx).symm)
  ·
    obtain ⟨p, hp_mem, hp_min⟩ := hcompact.exists_isMinOn hne_closure huc
    by_cases hp_in : p ∈ Ω
    · exfalso
      have hmin_Ω : ∀ y ∈ Ω, u p ≤ u y := fun y hy => hp_min (subset_closure hy)
      have := CM7.strong_min_principle hΩo hΩc hmvp hp_in hmin_Ω
      exact hnot_const_at (fun y hy => (this y hy).trans (this x hx).symm)
    · have hp_frontier : p ∈ frontier Ω := by
      rw [frontier_eq_closure_inter_closure, Set.mem_inter_iff]
      exact ⟨hp_mem, by rwa [hΩo.isClosed_compl.closure_eq, Set.mem_compl_iff]⟩
      refine ⟨p, hp_frontier, ?_⟩
      have hle : u p ≤ u x := hp_min (subset_closure hx)
      obtain hlt | heq := lt_or_eq_of_le hle
      · exact hlt
      · exfalso
        have hmin_Ω : ∀ y ∈ Ω, u x ≤ u y := fun y hy =>
          heq ▸ hp_min (subset_closure hy)
        have := CM7.strong_min_principle hΩo hΩc hmvp hx hmin_Ω
        exact hnot_const_at (fun y hy => (this y hy).trans (this x hx).symm)

end CM6

namespace CM6

/--
[strong_max_principle_boundary_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM6/MeanValueStrongMax.lean)
-/
@[path]
lemma strong_max_principle_boundary_bounds
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
  {u : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}
-- given
  (hΩo : IsOpen Ω)
  (hΩc : IsConnected Ω)
  (hΩb : Bornology.IsBounded Ω)
  (hmvp : CM7.HasVolumeMVP u Ω)
  (huc : ContinuousOn u (closure Ω))
  (hnc : ¬ ∀ x ∈ Ω, ∀ y ∈ Ω, u x = u y)
  (hx : x ∈ Ω) :
-- imply
  u x < sSup (u '' frontier Ω) ∧ sInf (u '' frontier Ω) < u x := by
-- proof
  obtain ⟨⟨q₁, hq₁f, hlt₁⟩, ⟨q₂, hq₂f, hlt₂⟩⟩ :=
    strong_max_principle_bounded hΩo hΩc hΩb hmvp huc hnc hx
  have hfr_compact : IsCompact (frontier Ω) :=
    hΩb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hfr_img_bdd : BddAbove (u '' frontier Ω) :=
    (hfr_compact.image_of_continuousOn (huc.mono frontier_subset_closure)).isBounded.bddAbove
  have hfr_img_bdd_below : BddBelow (u '' frontier Ω) :=
    (hfr_compact.image_of_continuousOn (huc.mono frontier_subset_closure)).isBounded.bddBelow
  exact ⟨lt_of_lt_of_le hlt₁ (le_csSup hfr_img_bdd ⟨q₁, hq₁f, rfl⟩),
    lt_of_le_of_lt (csInf_le hfr_img_bdd_below ⟨q₂, hq₂f, rfl⟩) hlt₂⟩

end CM6

namespace CM6

/--
[strong_maximum_principle_full](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM6/MeanValueStrongMax.lean)
-/
@[path]
lemma strong_maximum_principle_full
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
  {u : (Fin n → ℝ) → ℝ}
-- given
  (hΩo : IsOpen Ω)
  (hΩc : IsConnected Ω)
  (hΩb : Bornology.IsBounded Ω)
  (hmvp : CM7.HasVolumeMVP u Ω)
  (huc : ContinuousOn u (closure Ω)) :
-- imply
  (∀ p ∈ Ω, (∀ x ∈ Ω, u x ≤ u p) ∨ (∀ x ∈ Ω, u p ≤ u x) → ∀ x ∈ Ω, u x = u p) ∧ (¬(∀ x ∈ Ω, ∀ y ∈ Ω, u x = u y) → ∀ x ∈ Ω, u x < sSup (u '' frontier Ω) ∧ sInf (u '' frontier Ω) < u x) :=
-- proof
  ⟨fun _p hp hextreme => strong_max_principle_combined hΩo hΩc hmvp hp hextreme,
    fun hnc _x hx => strong_max_principle_boundary_bounds hΩo hΩc hΩb hmvp huc hnc hx⟩

end CM6

namespace CM6

/--
[dirichlet_uniqueness_comparison_stability](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM6/MeanValueStrongMax.lean)
-/
@[path]
lemma dirichlet_uniqueness_comparison_stability
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
-- given
  (hn : 0 < n)
  (hΩo : IsOpen Ω)
  (hΩc : IsConnected Ω)
  (hΩb : Bornology.IsBounded Ω) :
-- imply
  (∀ u₁ u₂ : (Fin n → ℝ) → ℝ, CM7.IsHarmonic u₁ Ω → CM7.IsHarmonic u₂ Ω → (∀ x ∈ frontier Ω, u₁ x = u₂ x) → ContinuousOn u₁ (closure Ω) → ContinuousOn u₂ (closure Ω) → ∀ x ∈ Ω, u₁ x = u₂ x) ∧ (∀ u_f u_g : (Fin n → ℝ) → ℝ, CM7.IsHarmonic u_f Ω → CM7.IsHarmonic u_g Ω → ContinuousOn u_f (closure Ω) → ContinuousOn u_g (closure Ω) → (∀ x ∈ frontier Ω, u_f x ≥ u_g x) → (∃ y ∈ frontier Ω, u_f y > u_g y) → ∀ x ∈ Ω, u_f x > u_g x) ∧ (∀ u_f u_g : (Fin n → ℝ) → ℝ, CM7.IsHarmonic u_f Ω → CM7.IsHarmonic u_g Ω → ContinuousOn u_f (closure Ω) → ContinuousOn u_g (closure Ω) → ∀ f g : (Fin n → ℝ) → ℝ, ∀ M : ℝ, (∀ x ∈ frontier Ω, u_f x = f x) → (∀ x ∈ frontier Ω, u_g x = g x) → (∀ y ∈ frontier Ω, |f y - g y| ≤ M) → ∀ x ∈ Ω, |u_f x - u_g x| ≤ M) :=
-- proof
  ⟨fun _ _ h1 h2 hbdy hcont1 hcont2 =>
    CM7.dirichlet_uniqueness hn hΩo hΩc hΩb h1 h2 hbdy hcont1 hcont2,
    fun _ _ hf hg hcont_f hcont_g hbdy_ge hbdy_ne x hx =>
      CM7.comparison_principle hn hΩo hΩc hΩb hf hg hcont_f hcont_g hbdy_ge hbdy_ne x hx,
    fun _ _ huf hug huf_cont hug_cont _ _ _ huf_bd hug_bd hM x hx =>
      CM7.laplace_stability_estimate hn hΩo hΩc hΩb huf hug huf_cont hug_cont
        huf_bd hug_bd hM x hx⟩

end CM6


-- created on 2026-10-23
