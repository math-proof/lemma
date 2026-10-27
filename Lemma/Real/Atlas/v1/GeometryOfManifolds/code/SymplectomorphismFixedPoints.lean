import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.SymplectomorphismFixedPoints
open Filter Topology


/--
[closed_form_exact_zeros_eq_crit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplectomorphismFixedPoints.lean)
-/
@[path]
lemma closed_form_exact_zeros_eq_crit
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M]
  [ChartedSpace H M]
  {μ : M → (E →L[ℝ] ℝ)}
-- given
  (hμ_smooth : ContMDiff I (modelWithCornersSelf ℝ (E →L[ℝ] ℝ)) ⊤ μ)
  (hμ_closed : IsClosed1Form I μ)
  (hH1 : DeRhamH1Vanishes I M) :
-- imply
  ∃ (h : M → ℝ), ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ h ∧ (∀ x : M, μ x = 0 ↔ IsCriticalPt I h x) := by
-- proof
  obtain ⟨h, h_smooth, h_deriv⟩ := hH1 μ hμ_smooth hμ_closed
  exact ⟨h, h_smooth, fun x => by
    unfold IsCriticalPt
    constructor
    · intro hzero; rw [h_deriv x]; exact hzero
    · intro hcrit; rw [h_deriv x] at hcrit; exact hcrit⟩

/--
[mfderiv_eq_zero_of_isLocalMin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplectomorphismFixedPoints.lean)
-/
@[path]
lemma mfderiv_eq_zero_of_isLocalMin
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  [TopologicalSpace M]
  [ChartedSpace H M]
  [IsManifold I ⊤ M]
  {f : M → ℝ}
  {x : M}
-- given
  (hf : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f x)
  (hlmin : IsLocalMin f x) :
-- imply
  mfderiv I (modelWithCornersSelf ℝ ℝ) f x = 0 := by
-- proof
  simp only [mfderiv, hf, if_pos]
  have hrange : Set.range I = Set.univ := I.range_eq_univ
  rw [hrange, fderivWithin_univ]
  apply IsLocalMin.fderiv_eq_zero
  have hmap := map_extChartAt_nhds_of_boundaryless (I := I) (x := x)
  simp only [IsLocalMin, ← hmap, IsMinFilter, eventually_map]
  filter_upwards [hlmin, (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source (I := I) x)]
    with y hy hy_src
  simp only [writtenInExtChartAt, Function.comp, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, id]
  rwa [(extChartAt I x).left_inv hy_src, (extChartAt I x).left_inv (mem_extChartAt_source x)]

/--
[mfderiv_eq_zero_of_isLocalMax](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplectomorphismFixedPoints.lean)
-/
@[path]
lemma mfderiv_eq_zero_of_isLocalMax
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  [TopologicalSpace M]
  [ChartedSpace H M]
  [IsManifold I ⊤ M]
  {f : M → ℝ}
  {x : M}
-- given
  (hf : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f x)
  (hlmax : IsLocalMax f x) :
-- imply
  mfderiv I (modelWithCornersSelf ℝ ℝ) f x = 0 := by
-- proof
  simp only [mfderiv, hf, if_pos]
  have hrange : Set.range I = Set.univ := I.range_eq_univ
  rw [hrange, fderivWithin_univ]
  apply IsLocalMax.fderiv_eq_zero
  have hmap := map_extChartAt_nhds_of_boundaryless (I := I) (x := x)
  simp only [IsLocalMax, ← hmap, IsMaxFilter, eventually_map]
  filter_upwards [hlmax, (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source (I := I) x)]
    with y hy hy_src
  simp only [writtenInExtChartAt, Function.comp, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, id]
  rwa [(extChartAt I x).left_inv hy_src, (extChartAt I x).left_inv (mem_extChartAt_source x)]

/--
[compact_manifold_two_critical_points](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplectomorphismFixedPoints.lean)
-/
@[path]
lemma compact_manifold_two_critical_points
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  [TopologicalSpace M]
  [ChartedSpace H M]
  [IsManifold I ⊤ M]
  [CompactSpace M]
  [Nontrivial M]
  {f : M → ℝ}
-- given
  (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ f) :
-- imply
  ∃ x y : M, x ≠ y ∧ IsCriticalPt I f x ∧ IsCriticalPt I f y := by
-- proof
  have hne : (Set.univ : Set M).Nonempty := Set.univ_nonempty
  have hcont : ContinuousOn f Set.univ := hf.continuous.continuousOn
  obtain ⟨xmin, _, hxmin⟩ := isCompact_univ.exists_isMinOn hne hcont
  obtain ⟨xmax, _, hxmax⟩ := isCompact_univ.exists_isMaxOn hne hcont
  by_cases hne_pts : xmin ≠ xmax
  ·
    refine ⟨xmin, xmax, hne_pts, ?_, ?_⟩
    ·
      exact mfderiv_eq_zero_of_isLocalMin (hf.mdifferentiableAt (by simp))
        (hxmin.isLocalMin (isOpen_univ.mem_nhds (Set.mem_univ _)))
    ·
      exact mfderiv_eq_zero_of_isLocalMax (hf.mdifferentiableAt (by simp))
        (hxmax.isLocalMax (isOpen_univ.mem_nhds (Set.mem_univ _)))
  ·
    simp only [not_not] at hne_pts
    subst hne_pts
    have hconst : ∀ y : M, f y = f xmin := by
      intro y
      have hle : f xmin ≤ f y := hxmin (Set.mem_univ y)
      have hge : f y ≤ f xmin := hxmax (Set.mem_univ y)
      linarith
    obtain ⟨a, b, hab⟩ := exists_pair_ne M
    refine ⟨a, b, hab, ?_, ?_⟩ <;> {
      unfold IsCriticalPt
      have heq : f = fun _ => f xmin := funext hconst
      rw [heq, mfderiv_const]
    }
/-- Symplectomorphism fixed-point theorem (Theorem 1): for compact $(M, \omega)$ with $H^1(M, \mathbb{R}) = 0$, every symplectomorphism $C^1$-close to the identity has at least two distinct fixed points. -/


-- created on 2026-10-23
