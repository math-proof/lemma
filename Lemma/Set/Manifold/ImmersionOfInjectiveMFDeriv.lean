import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Geometry.Manifold.ImmersionOfInjectiveMFDeriv
open scoped Topology ContDiff
open Function Set Manifold
open MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDerivWanted


/--
[immersionInj_iftHomeomorph](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionOfInjectiveMFDeriv.lean)
-/
@[path]
private lemma immersionInj_iftHomeomorph
  {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω} {g : E → F} {U : Set E} {a : E} {g' : E ≃L[𝕜] F}
  (hn : 1 ≤ n) (hU : IsOpen U) (ha : a ∈ U) (hg : ContDiffOn 𝕜 n g U)
  (hderiv : HasFDerivAt g (g' : E →L[𝕜] F) a) :
  ∃ h : OpenPartialHomeomorph E F, a ∈ h.source ∧ h.source ⊆ U ∧
    ⇑h = g ∧ ContDiffOn 𝕜 n h h.source ∧ ContDiffOn 𝕜 n h.symm h.target := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  have hga : ContDiffAt 𝕜 n g a := hg.contDiffAt (hU.mem_nhds ha)
  have hcont : ContinuousOn (fderiv 𝕜 g) U :=
    hg.continuousOn_fderiv_of_isOpen hU hn
  set W : Set E := U ∩ (fderiv 𝕜 g) ⁻¹'
    Set.range ContinuousLinearEquiv.toContinuousLinearMap with hWdef
  have hWopen : IsOpen W := by
    rw [hWdef]
    exact hcont.isOpen_inter_preimage hU ContinuousLinearEquiv.isOpen
  have haW : a ∈ W := by
    refine ⟨ha, g', ?_⟩
    exact hderiv.fderiv.symm
  set h0 := hga.toOpenPartialHomeomorph g hderiv hn0 with hh0def
  have h0coe : ⇑h0 = g := ContDiffAt.toOpenPartialHomeomorph_coe hga hderiv hn0
  have hamem : a ∈ h0.source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source hga hderiv hn0
  set h := h0.restrOpen W hWopen with hhdef
  have hcoe : ⇑h = g := by
    rwa [hhdef, OpenPartialHomeomorph.coe_restrOpen]
  have hsource : h.source = h0.source ∩ W := by
    rw [hhdef]
    exact OpenPartialHomeomorph.restrOpen_source h0 W hWopen
  refine ⟨h, ?_, ?_, hcoe, ?_, ?_⟩
  · rw [hsource]
    exact ⟨hamem, haW⟩
  · intro z hz
    rwa [hsource, hWdef] at hz
  · rw [hcoe]
    exact hg.mono fun z hz => by
      rwa [hsource, hWdef] at hz
  · intro y hy
    have hxy : h.symm y ∈ h0.source ∩ W := by
      have hbase : h.symm y ∈ h.source := h.map_target hy
      rwa [hsource] at hbase
    obtain ⟨-, hxU, hxrange⟩ := hWdef ▸ hxy
    obtain ⟨e, he⟩ := hxrange
    have hAt : ContDiffAt 𝕜 n g (h.symm y) := hg.contDiffAt (hU.mem_nhds hxU)
    have hHas : HasFDerivAt g (e : E →L[𝕜] F) (h.symm y) := by
      have hbase := (hAt.differentiableAt hn0).hasFDerivAt
      rwa [← he] at hbase
    have hHas' : HasFDerivAt h (e : E →L[𝕜] F) (h.symm y) := by
      rwa [hcoe]
    have hAt' : ContDiffAt 𝕜 n h (h.symm y) := by
      rwa [hcoe]
    exact (h.contDiffAt_symm hy hHas' hAt').contDiffWithinAt

/--
[immersionInj_contDiffOn_writtenInExtChartAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionOfInjectiveMFDeriv.lean)
-/
@[path]
private lemma immersionInj_contDiffOn_writtenInExtChartAt
  {𝕜 E E' H G M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {x : M} (hfn : ∀ᶠ y in 𝓝 x, ContMDiffAt I J n f y) :
  ∃ U : Set E, IsOpen U ∧ extChartAt I x x ∈ U ∧
    ContDiffOn 𝕜 n (writtenInExtChartAt I J x f) U := by
  obtain ⟨s, hs, hsopen, hxs⟩ := eventually_nhds_iff.mp hfn
  have hcont : ContinuousOn f s := fun y hy =>
    (hs y hy).continuousAt.continuousWithinAt
  set W : Set M :=
    (s ∩ f ⁻¹' (chartAt G (f x)).source) ∩ (chartAt H x).source with hWdef
  have hWopen : IsOpen W := by
    rw [hWdef]
    exact (hcont.isOpen_inter_preimage hsopen (chartAt G (f x)).open_source).inter
      (chartAt H x).open_source
  have hxW : x ∈ W := by
    rw [hWdef]
    exact ⟨⟨hxs, mem_chart_source G (f x)⟩, mem_chart_source H x⟩
  have hWsource : W ⊆ (extChartAt I x).source := by
    intro y hy
    rw [extChartAt_source]
    exact (hWdef ▸ hy).2
  have hWmaps : MapsTo f W (extChartAt J (f x)).source := by
    intro y hy
    rw [extChartAt_source]
    exact (hWdef ▸ hy).1.2
  have hWdiff : ContMDiffOn I J n f W := fun y hy =>
    (hs y (hWdef ▸ hy).1.1).contMDiffWithinAt
  have hcoord : ContDiffOn 𝕜 n (writtenInExtChartAt I J x f) (extChartAt I x '' W) :=
    (contMDiffOn_iff_of_subset_source' hWsource hWmaps).mp hWdiff
  set domExt : OpenPartialHomeomorph M E :=
    (chartAt H x).transHomeomorph I.toHomeomorph with hdomExtdef
  have hdomExtCoe : ⇑domExt = extChartAt I x := rfl
  have hUopen : IsOpen (extChartAt I x '' W) := by
    rw [← hdomExtCoe]
    apply domExt.isOpen_image_of_subset_source hWopen
    simpa [domExt, hdomExtdef] using hWsource
  exact ⟨extChartAt I x '' W, hUopen, ⟨x, hxW, rfl⟩, hcoord⟩

/--
[immersionInj_complementEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionOfInjectiveMFDeriv.lean)
-/
@[path]
private lemma immersionInj_complementEquiv
  {𝕜 E E' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
  (L : E →L[𝕜] E') (hinj : Function.Injective L)
  (hcompl : L.range.ClosedComplemented) :
  ∃ e : (E × hcompl.complement) ≃L[𝕜] E',
    ∀ z, e z = L z.1 + z.2 := by
  let eRange : E ≃L[𝕜] L.range := L.equivRange hinj hcompl.isClosed
  let eProd : (E × hcompl.complement) ≃L[𝕜] (L.range × hcompl.complement) :=
    ContinuousLinearEquiv.prodCongr eRange (ContinuousLinearEquiv.refl 𝕜 hcompl.complement)
  let e : (E × hcompl.complement) ≃L[𝕜] E' :=
    eProd.trans <| L.range.prodEquivOfIsTopCompl hcompl.complement
      hcompl.isTopCompl_complement
  refine ⟨e, fun z => ?_⟩
  simp [e, eProd, eRange, Submodule.prodEquivOfIsTopCompl_apply]
  rfl

/--
[immersionInj_codChart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionOfInjectiveMFDeriv.lean)
-/
@[path]
private lemma immersionInj_codChart
  {𝕜 E' F G N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace G] {J : ModelWithCorners 𝕜 E' G} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω} [IsManifold J n N]
  (q : OpenPartialHomeomorph F E') (e : F ≃L[𝕜] E')
  (hq : ContDiffOn 𝕜 n q q.source)
  (hqsymm : ContDiffOn 𝕜 n q.symm q.target) (y : N)
  (hyq : extChartAt J y y ∈ q.target) :
  ∃ c : OpenPartialHomeomorph N G, y ∈ c.source ∧
    c ∈ IsManifold.maximalAtlas J n N ∧
    ⇑(c.extend J) = e ∘ q.symm ∘ extChartAt J y := by
  let c0 : OpenPartialHomeomorph N E' :=
    (chartAt G y).transHomeomorph J.toHomeomorph
  let r : OpenPartialHomeomorph E' E' :=
    q.symm.transHomeomorph e.toHomeomorph
  let cE : OpenPartialHomeomorph N E' := c0.trans r
  let c : OpenPartialHomeomorph N G := cE.transHomeomorph J.toHomeomorph.symm
  have hc0 : ContMDiffOn J 𝓘(𝕜, E') n c0 c0.source := by
    have hfun : (c0 : N → E') = (chartAt G y).extend J := by
      funext z
      rfl
    have hsource : c0.source = (chartAt G y).source := rfl
    rw [hfun, hsource]
    exact (chartAt G y).contMDiffOn_extend (IsManifold.chart_mem_maximalAtlas y)
  have hc0symm : ContMDiffOn 𝓘(𝕜, E') J n c0.symm c0.target := by
    have hfun : (c0.symm : E' → N) = ((chartAt G y).extend J).symm := by
      funext z
      rfl
    have htarget : c0.target = J '' (chartAt G y).target := by
      change J.symm ⁻¹' (chartAt G y).target = J '' (chartAt G y).target
      rw [J.image_eq, J.range_eq_univ, inter_univ]
    rw [hfun, htarget]
    exact contMDiffOn_extend_symm (IsManifold.chart_mem_maximalAtlas (I := J) y)
  have hr : ContDiffOn 𝕜 n r r.source := by
    have h := e.contDiff.contDiffOn.comp hqsymm (mapsTo_univ _ _)
    simpa [r] using h
  have hrsymm : ContDiffOn 𝕜 n r.symm r.target := by
    have htarget : r.target = e.symm ⁻¹' q.source := by
      ext z
      simp [r]
    rw [htarget]
    change ContDiffOn 𝕜 n (q ∘ e.symm) (fun z => e.symm z ∈ q.source)
    exact hq.comp e.symm.contDiff.contDiffOn (fun _ hz => hz)
  have hcE : ContMDiffOn J 𝓘(𝕜, E') n cE cE.source := by
    have hsource : cE.source ⊆ c0.source := by
      intro z hz
      change z ∈ (c0.trans r).source at hz
      rwa [OpenPartialHomeomorph.trans_source] at hz
    have hmaps : MapsTo c0 cE.source r.source := by
      intro z hz
      change z ∈ (c0.trans r).source at hz
      rwa [OpenPartialHomeomorph.trans_source] at hz
    have h := hr.contMDiffOn.comp (hc0.mono hsource) hmaps
    simpa [cE] using h
  have hcEsymm : ContMDiffOn 𝓘(𝕜, E') J n cE.symm cE.target := by
    have htarget : cE.target ⊆ r.target := by
      intro z hz
      change z ∈ (c0.trans r).target at hz
      rwa [OpenPartialHomeomorph.trans_target] at hz
    have hmaps : MapsTo r.symm cE.target c0.target := by
      intro z hz
      change z ∈ (c0.trans r).target at hz
      rwa [OpenPartialHomeomorph.trans_target] at hz
    have h := hc0symm.comp (hrsymm.contMDiffOn.mono htarget) hmaps
    simpa [cE] using h
  have hc : ContMDiffOn J J n c c.source := by
    change ContMDiffOn J J n (J.symm ∘ cE) cE.source
    exact J.contMDiffOn_symm.comp hcE fun _ _ => by
      rw [J.range_eq_univ]
      exact mem_univ _
  have hcsymm : ContMDiffOn J J n c.symm c.target := by
    change ContMDiffOn J J n (cE.symm ∘ J) (J ⁻¹' cE.target)
    exact hcEsymm.comp J.contMDiff.contMDiffOn fun _ hz => hz
  refine ⟨c, ?_, c.mem_maximalAtlas_of_contMDiffOn hc hcsymm, ?_⟩
  · change y ∈ (c0.trans r).source
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · change y ∈ (chartAt G y).source
      exact mem_chart_source G y
    · change extChartAt J y y ∈ q.target
      exact hyq
  · funext z
    simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply]
    change J (J.symm (e (q.symm (extChartAt J y z)))) = _
    rw [J.right_inv]
    simp [J.range_eq_univ]

/--
[Manifold.IsImmersionAt.of_injective_mfderiv_of_closedComplemented_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionOfInjectiveMFDeriv.lean)
-/
@[path]
lemma Manifold.IsImmersionAt.of_injective_mfderiv_of_closedComplemented_range
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E'] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E' G} [J.Boundaryless]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N}
  {x : M}
-- given
  (hn : 1 ≤ n)
  (hfn : ∀ᶠ y in 𝓝 x, ContMDiffAt I J n f y)
  (hderiv : Function.Injective (mfderiv I J f x : E →L[𝕜] E'))
  (hcompl : (mfderiv I J f x : E →L[𝕜] E').range.ClosedComplemented) :
-- imply
  IsImmersionAt I J n f x := by
-- proof
  let L : E →L[𝕜] E' := (mfderiv I J f x : E →L[𝕜] E')
  change L.range.ClosedComplemented at hcompl
  let : CompleteSpace hcompl.complement := hcompl.isClosed_complement.completeSpace_coe
  obtain ⟨e, he⟩ := immersionInj_complementEquiv L hderiv hcompl
  obtain ⟨U, hUopen, hxU, hgU⟩ :=
    immersionInj_contDiffOn_writtenInExtChartAt hfn
  let g : E → E' := writtenInExtChartAt I J x f
  let x0 : E := extChartAt I x x
  have hfx : ContMDiffAt I J n f x := hfn.self_of_nhds
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  have hmd : MDifferentiableAt I J f x := hfx.mdifferentiableAt hn0
  have hfg : HasFDerivAt g L x0 := by
    have hdiff : DifferentiableAt 𝕜 g x0 := by
      simpa [g, x0, I.range_eq_univ, differentiableWithinAt_univ] using
        hmd.differentiableWithinAt_writtenInExtChartAt
    have hbase := hdiff.hasFDerivAt
    have hLeq : fderiv 𝕜 g x0 = L := by
      have h := hmd.mfderiv_abuse
      change L = fderivWithin 𝕜 g (Set.range I) x0 at h
      simpa [I.range_eq_univ] using h.symm
    rwa [hLeq] at hbase
  let incl : (E × hcompl.complement) →L[𝕜] E' :=
    hcompl.complement.subtypeL.comp
      (ContinuousLinearMap.snd 𝕜 E hcompl.complement)
  let Ψ : E × hcompl.complement → E' := fun z => g z.1 + (z.2 : E')
  have hΨsmooth : ContDiffOn 𝕜 n Ψ (U ×ˢ (Set.univ : Set hcompl.complement)) := by
    have hfirst : ContDiffOn 𝕜 n (g ∘ Prod.fst)
      (U ×ˢ (Set.univ : Set hcompl.complement)) :=
      hgU.comp contDiffOn_fst fun _ hz => hz.1
    have hsecond : ContDiffOn 𝕜 n incl
      (U ×ˢ (Set.univ : Set hcompl.complement)) :=
      incl.contDiff.contDiffOn
    simpa [Ψ, incl, Function.comp_def] using hfirst.add hsecond
  have hΨderiv : HasFDerivAt Ψ
    (e : (E × hcompl.complement) →L[𝕜] E') (x0, 0) := by
    have hfst : HasFDerivAt (Prod.fst : E × hcompl.complement → E)
      (ContinuousLinearMap.fst 𝕜 E hcompl.complement)
      (x0, (0 : hcompl.complement)) := hasFDerivAt_fst
    have hfirst := hfg.comp (x0, (0 : hcompl.complement)) hfst
    have hsecond : HasFDerivAt incl incl (x0, (0 : hcompl.complement)) :=
      incl.hasFDerivAt
    have hsum := hfirst.add hsecond
    have hmap : L.comp (ContinuousLinearMap.fst 𝕜 E hcompl.complement) + incl =
      (e : (E × hcompl.complement) →L[𝕜] E') := by
      apply ContinuousLinearMap.ext
      intro z
      change L z.1 + (z.2 : E') = e z
      rw [he]
    rw [hmap] at hsum
    convert hsum using 1
    ext z
    simp [Ψ, incl, Function.comp_def]
  obtain ⟨q, hxq, hqsource, hqcoe, hqsmooth, hqsymmsmooth⟩ :=
    immersionInj_iftHomeomorph (g := Ψ)
      (U := U ×ˢ (Set.univ : Set hcompl.complement))
      (a := (x0, (0 : hcompl.complement))) (g' := e) hn
      (hUopen.prod isOpen_univ)
      ⟨hxU, mem_univ (0 : hcompl.complement)⟩ hΨsmooth hΨderiv
  have hyq : extChartAt J (f x) (f x) ∈ q.target := by
    have h := q.map_source hxq
    rw [congrFun hqcoe (x0, 0)] at h
    simpa [Ψ, g, x0, writtenInExtChartAt, extChartAt_to_inv] using h
  obtain ⟨codChart, hfxcod, hcodAtlas, hcodEq⟩ :=
    immersionInj_codChart q e hqsmooth hqsymmsmooth (f x) hyq
  set V : Set E := (fun u => (u, (0 : hcompl.complement))) ⁻¹' q.source with hVdef
  have hVopen : IsOpen V := q.open_source.preimage (continuous_id.prodMk continuous_const)
  have hxV : x0 ∈ V := hxq
  set s : Set M := (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' V with hsdef
  have hsopen : IsOpen s := by
    rw [hsdef]
    exact (continuousOn_extChartAt x).isOpen_inter_preimage
      (isOpen_extChartAt_source x) hVopen
  have hxs : x ∈ s := by
    rw [hsdef]
    exact ⟨mem_extChartAt_source x, hxV⟩
  let domChart : OpenPartialHomeomorph M H := (chartAt H x).restr s
  have hxdom : x ∈ domChart.source := by
    change x ∈ ((chartAt H x).restr s).source
    rw [OpenPartialHomeomorph.restr_source' (chartAt H x) s hsopen]
    exact ⟨mem_chart_source H x, hxs⟩
  have hdomAtlas : domChart ∈ IsManifold.maximalAtlas I n M := by
    exact restr_mem_maximalAtlas (contDiffGroupoid n I)
      (IsManifold.chart_mem_maximalAtlas x) hsopen
  apply IsImmersionAt.mk_of_continuousAt hfx.continuousAt e domChart codChart
    hxdom hfxcod hdomAtlas hcodAtlas
  intro u hu
  have hydom : (domChart.extend I).symm u ∈ domChart.source := by
    have h := (domChart.extend I).map_target hu
    rwa [OpenPartialHomeomorph.extend_source] at h
  have hys : (domChart.extend I).symm u ∈ s := by
    change (domChart.extend I).symm u ∈ ((chartAt H x).restr s).source at hydom
    rwa [OpenPartialHomeomorph.restr_source' (chartAt H x) s hsopen] at hydom
  have hueq : extChartAt I x ((domChart.extend I).symm u) = u := by
    have h := (domChart.extend I).right_inv hu
    exact h
  have huq : (u, (0 : hcompl.complement)) ∈ q.source := by
    have := (hsdef ▸ hys).2
    rw [hVdef] at this
    change (extChartAt I x ((domChart.extend I).symm u), 0) ∈ q.source at this
    rwa [hueq] at this
  change codChart.extend J (f ((domChart.extend I).symm u)) = e (u, 0)
  rw [congrFun hcodEq (f ((domChart.extend I).symm u))]
  change e (q.symm (g u)) = e (u, 0)
  have hqu : q (u, (0 : hcompl.complement)) = g u := by
    rw [congrFun hqcoe (u, 0)]
    simp [Ψ]
  rw [← hqu, q.left_inv huq]
namespace MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDerivWanted
universe u
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} {E'' : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G}
variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
variable {n : ℕ∞ω}

namespace MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDerivWanted

/--
[immersionAt_of_injective_mfderiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionOfInjectiveMFDeriv.lean)
-/
@[path]
lemma immersionAt_of_injective_mfderiv
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [CompleteSpace 𝕜] [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E]
  {E'' : Type u} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [FiniteDimensional 𝕜 E'']
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N}
  {x : M}
-- given
  (hn : 1 ≤ n)
  (hfn : ∀ᶠ y in 𝓝 x, ContMDiffAt I J n f y)
  (hderiv : Function.Injective (mfderiv I J f x)) :
-- imply
  IsImmersionAt I J n f x := by
-- proof
  let _ : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let _ : CompleteSpace E'' := FiniteDimensional.complete 𝕜 E''
  change Function.Injective (mfderiv I J f x : E →L[𝕜] E'') at hderiv
  apply Manifold.IsImmersionAt.of_injective_mfderiv_of_closedComplemented_range
    (E := E) (E' := E'') hn hfn hderiv
  let L : E →L[𝕜] E'' := (mfderiv I J f x : E →L[𝕜] E'')
  change L.range.ClosedComplemented
  exact Submodule.ClosedComplemented.of_finiteDimensional _

end MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDerivWanted


-- created on 2026-10-20
-- updated on 2026-10-26
