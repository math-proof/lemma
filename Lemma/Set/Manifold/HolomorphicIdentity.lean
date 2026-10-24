import Mathlib
import sympy.Basic
open Set Manifold
open scoped Manifold


namespace MDifferentiable

/--
[holomorphic_identity_aux_complete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/HolomorphicIdentity.lean)
-/
@[path]
reducing to the one-dimensional analytic identity theorem along complex lines
in charts. -/
private theorem holomorphic_identity_aux_complete
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [ConnectedSpace M]
  {f g : M → F} (hf : MDiff f) (hg : MDiff g)
  {U : Set M} (hU_open : IsOpen U) (hU_nonempty : U.Nonempty) (h_eq : EqOn f g U) :
  f = g := by
  -- The set of points near which `f` and `g` agree.
  set S : Set M := {x | ∃ o : Set M, IsOpen o ∧ x ∈ o ∧ EqOn f g o} with hSdef
  have hS_open : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨o, ho_open, hxo, hfg⟩ := hx
    exact ⟨o, fun y hy => ⟨o, ho_open, hy, hfg⟩, ho_open, hxo⟩
  have hUS : U ⊆ S := fun x hx => ⟨U, hU_open, hx, h_eq⟩
  have hS_ne : S.Nonempty := hU_nonempty.mono hUS
  -- Coordinate representations of differentiable maps are differentiable on chart targets.
  have hdiff_of : ∀ {h : M → F}, MDiff h → ∀ (x : M),
    DifferentiableOn ℂ (h ∘ (extChartAt I x).symm) (extChartAt I x).target := by
    intro h hh x
    have h1 :=
      (mdifferentiableOn_iff.mp (hh.mdifferentiableOn (s := Set.univ))).2 x (h x)
    simp only [extChartAt_model_space_eq_id] at h1
    simpa using h1
  -- `S` is closed: agreement propagates across charts via complex lines.
  have hsub : closure S ⊆ S := by
    intro x hx
    have hx_src : x ∈ (extChartAt I x).source := by
      rw [extChartAt_source]
      exact mem_chart_source H x
    have hsrc_open : IsOpen (extChartAt I x).source := isOpen_extChartAt_source x
    have htgt_open : IsOpen (extChartAt I x).target := isOpen_extChartAt_target x
    have hc_mem : (extChartAt I x) x ∈ (extChartAt I x).target :=
      mem_of_mem_nhds (extChartAt_target_mem_nhds x)
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.mem_nhds_iff.mp (htgt_open.mem_nhds hc_mem)
    have hN_open : IsOpen
      ((extChartAt I x).source ∩ (extChartAt I x) ⁻¹' Metric.ball ((extChartAt I x) x) r) := by
      rw [extChartAt_source]
      exact isOpen_extChartAt_preimage x Metric.isOpen_ball
    have hxN : x ∈
      (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' Metric.ball ((extChartAt I x) x) r :=
      ⟨hx_src, Metric.mem_ball_self hr_pos⟩
    obtain ⟨y, hyN, hyS⟩ := mem_closure_iff_nhds.mp hx _ (hN_open.mem_nhds hxN)
    obtain ⟨o, ho_open, hyo, hfg_o⟩ := hyS
    have hy_symm : (extChartAt I x).symm ((extChartAt I x) y) = y :=
      PartialEquiv.left_inv _ hyN.1
    have hcont : ContinuousAt (extChartAt I x).symm ((extChartAt I x) y) :=
      (continuousOn_extChartAt_symm x).continuousAt (htgt_open.mem_nhds (hr_sub hyN.2))
    have htend : Filter.Tendsto (extChartAt I x).symm (nhds ((extChartAt I x) y)) (nhds y) := by
      have h2 : Filter.Tendsto (extChartAt I x).symm (nhds ((extChartAt I x) y))
        (nhds ((extChartAt I x).symm ((extChartAt I x) y))) := hcont
      rwa [hy_symm] at h2
    have hmem : ∀ᶠ z in nhds ((extChartAt I x) y), (extChartAt I x).symm z ∈ o :=
      htend.eventually (Filter.eventually_of_mem (ho_open.mem_nhds hyo) (fun _ hw => hw))
    have hFG_event : (f ∘ (extChartAt I x).symm) =ᶠ[nhds ((extChartAt I x) y)]
      (g ∘ (extChartAt I x).symm) :=
      hmem.mono (fun z hz => hfg_o hz)
    -- The representatives agree on the whole ball: check one complex line at a time.
    have hEqB : EqOn (f ∘ (extChartAt I x).symm) (g ∘ (extChartAt I x).symm)
      (Metric.ball ((extChartAt I x) x) r) := by
      intro z₁ hz₁B
      set v : E := z₁ - (extChartAt I x) y with hv
      set ℓ : ℂ → E := fun t => (extChartAt I x) y + t • v with hℓ
      have hℓ0 : ℓ 0 = (extChartAt I x) y := by simp [hℓ]
      have hℓ1 : ℓ 1 = z₁ := by simp [hℓ, hv]
      have hℓ_diff : Differentiable ℂ ℓ :=
        ((differentiable_id.smul_const v).const_add ((extChartAt I x) y))
      have hℓ_cont : Continuous ℓ := hℓ_diff.continuous
      set W : Set ℂ := ℓ ⁻¹' Metric.ball ((extChartAt I x) x) r with hW
      have hW_open : IsOpen W := Metric.isOpen_ball.preimage hℓ_cont
      have h0W : (0 : ℂ) ∈ W := by
        change ℓ 0 ∈ Metric.ball _ _
        rwa [hℓ0]
      have h1W : (1 : ℂ) ∈ W := by
        change ℓ 1 ∈ Metric.ball _ _
        rwa [hℓ1]
      have hW_convex : Convex ℝ W := by
        intro a ha b hb u w hu hw huw
        change ℓ (u • a + w • b) ∈ Metric.ball _ _
        have haff : ℓ (u • a + w • b) = u • ℓ a + w • ℓ b := by
          simp only [hℓ]
          rw [smul_add, smul_add, add_smul, ← smul_assoc u a v, ← smul_assoc w b v]
          have hrearr : (u • (extChartAt I x) y + (u • a) • v) +
            (w • (extChartAt I x) y + (w • b) • v) =
            (u • (extChartAt I x) y + w • (extChartAt I x) y) +
            ((u • a) • v + (w • b) • v) := by
            abel
          rw [hrearr, ← add_smul u w _, huw, one_smul]
        rw [haff]
        exact (convex_ball _ _) ha hb hu hw huw
      have hW_pre : IsPreconnected W := hW_convex.isPreconnected
      have hmaps : MapsTo ℓ W (Metric.ball ((extChartAt I x) x) r) := fun t ht => ht
      have hF_slice : DifferentiableOn ℂ ((f ∘ (extChartAt I x).symm) ∘ ℓ) W :=
        ((hdiff_of hf x).mono hr_sub).comp (hℓ_diff.differentiableOn (s := W)) hmaps
      have hG_slice : DifferentiableOn ℂ ((g ∘ (extChartAt I x).symm) ∘ ℓ) W :=
        ((hdiff_of hg x).mono hr_sub).comp (hℓ_diff.differentiableOn (s := W)) hmaps
      have hF_an : AnalyticOnNhd ℂ ((f ∘ (extChartAt I x).symm) ∘ ℓ) W :=
        hW_open.analyticOn_iff_analyticOnNhd.mp (hF_slice.analyticOn hW_open)
      have hG_an : AnalyticOnNhd ℂ ((g ∘ (extChartAt I x).symm) ∘ ℓ) W :=
        hW_open.analyticOn_iff_analyticOnNhd.mp (hG_slice.analyticOn hW_open)
      have htend0 : Filter.Tendsto ℓ (nhds (0 : ℂ)) (nhds ((extChartAt I x) y)) := by
        rw [← hℓ0]
        exact hℓ_cont.tendsto 0
      have hslice_event : ((f ∘ (extChartAt I x).symm) ∘ ℓ) =ᶠ[nhds (0 : ℂ)]
        ((g ∘ (extChartAt I x).symm) ∘ ℓ) :=
        hFG_event.comp_tendsto htend0
      have hEqW :=
        AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF_an hG_an hW_pre h0W hslice_event
      have h1 := hEqW h1W
      simp only [Function.comp_apply, hℓ1] at h1
      exact h1
    have hfg_N : EqOn f g
      ((extChartAt I x).source ∩ (extChartAt I x) ⁻¹' Metric.ball ((extChartAt I x) x) r) := by
      intro w hw
      have hwB := hEqB hw.2
      rw [Function.comp_apply, Function.comp_apply] at hwB
      rwa [PartialEquiv.left_inv _ hw.1] at hwB
    exact ⟨_, hN_open, hxN, hfg_N⟩
  have hS_closed : IsClosed S := closure_eq_iff_isClosed.mp (le_antisymm hsub subset_closure)
  have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
  have hSuniv : S = Set.univ := hS_clopen.eq_univ hS_ne
  funext x
  have hxS : x ∈ S := by
    rw [hSuniv]
    exact Set.mem_univ x
  obtain ⟨o, -, hxo, hfg⟩ := hxS
  exact hfg hxo

end MDifferentiable

namespace MDifferentiable

/--
[eq_of_eqOn_of_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/HolomorphicIdentity.lean)
-/
@[path]
lemma eq_of_eqOn_of_isOpen
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [ConnectedSpace M]
  {I : ModelWithCorners ℂ E H} [I.Boundaryless] [IsManifold I 1 M]
  {f g : M → F}
  {U : Set M}
-- given
  (hf : MDiff f)
  (hg : MDiff g)
  (hU_open : IsOpen U)
  (hU_nonempty : U.Nonempty)
  (h_eq : EqOn f g U) :
-- imply
  f = g := by
-- proof
  let ι : F →L[ℂ] UniformSpace.Completion F :=
    (UniformSpace.Completion.toComplₗᵢ : F →ₗᵢ[ℂ] UniformSpace.Completion F).toContinuousLinearMap
  have hι : MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, UniformSpace.Completion F) ⇑ι :=
    (ι.differentiable).mdifferentiable
  have hf' : MDifferentiable I 𝓘(ℂ, UniformSpace.Completion F) (⇑ι ∘ f) :=
    MDifferentiable.comp hι hf
  have hg' : MDifferentiable I 𝓘(ℂ, UniformSpace.Completion F) (⇑ι ∘ g) :=
    MDifferentiable.comp hι hg
  have h_eq' : EqOn (⇑ι ∘ f) (⇑ι ∘ g) U := fun x hx => congrArg _ (h_eq hx)
  have hmain := holomorphic_identity_aux_complete hf' hg' hU_open hU_nonempty h_eq'
  have hinj : Function.Injective ⇑ι :=
    (UniformSpace.Completion.toComplₗᵢ : F →ₗᵢ[ℂ] UniformSpace.Completion F).injective
  funext x
  apply hinj
  exact congrFun hmain x
end MDifferentiable


namespace MathlibExt.Geometry.Manifold.ComplexRigidityWanted

/--
[holomorphic_identity_on_connected_complex_manifold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/HolomorphicIdentity.lean)
-/
@[path]
lemma holomorphic_identity_on_connected_complex_manifold
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [ConnectedSpace M]
  {I : ModelWithCorners ℂ E H} [I.Boundaryless] [IsManifold I 1 M]
  {f g : M → F}
  {U : Set M}
-- given
  (hf : MDiff f)
  (hg : MDiff g)
  (hU_open : IsOpen U)
  (hU_nonempty : U.Nonempty)
  (h_eq : EqOn f g U) :
-- imply
  f = g :=
-- proof
  MDifferentiable.eq_of_eqOn_of_isOpen hf hg hU_open hU_nonempty h_eq

end MathlibExt.Geometry.Manifold.ComplexRigidityWanted


-- created on 2026-10-20
-- updated on 2026-10-23
