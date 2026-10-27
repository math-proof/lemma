import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Geometry.Manifold.OneDimensional.Part11
open scoped Manifold ContDiff Topology Bundle
open scoped Manifold ContDiff
open MathlibExt.Geometry.Manifold.OneDimensionalClassification
open MathlibExt.Geometry.Manifold.OneDimensionalWanted


namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G} [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}
/--
[odm_exists_partialDiffeomorph_of_invOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma odm_exists_partialDiffeomorph_of_invOn
  (f : M → N) (f' : N → M) (U : Set M) (V : Set N)
  (hU : IsOpen U) (hV : IsOpen V)
  (hf : Set.MapsTo f U V) (hf' : Set.MapsTo f' V U)
  (h : Set.InvOn f' f U V)
  (hfD : ContMDiffOn I J n f U) (hf'D : ContMDiffOn J I n f' V) :
  ∃ Φ : PartialDiffeomorph I J M N n, Φ.source = U ∧ Φ.target = V ∧
    (⇑Φ : M → N) = f ∧ Set.EqOn ⇑Φ.symm f' V := by
  refine ⟨PartialDiffeomorph.mk
    { toFun := f, invFun := f', source := U, target := V,
      map_source' := hf, map_target' := hf', left_inv' := h.1, right_inv' := h.2 }
    hU hV hfD hf'D, rfl, rfl, rfl, ?_⟩
  intro y _
  rfl

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G} [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}
/--
[odm_isLocalDiffeomorphAt_of_invOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma odm_isLocalDiffeomorphAt_of_invOn
  (f : M → N) (f' : N → M) (U : Set M) (V : Set N)
  (hU : IsOpen U) (hV : IsOpen V)
  (hf : Set.MapsTo f U V) (hf' : Set.MapsTo f' V U)
  (h : Set.InvOn f' f U V)
  (hfD : ContMDiffOn I J n f U) (hf'D : ContMDiffOn J I n f' V)
  (x : M) (hx : x ∈ U) : IsLocalDiffeomorphAt I J n f x := by
  obtain ⟨Φ, hsrc, _, hfu, _⟩ :=
    odm_exists_partialDiffeomorph_of_invOn f f' U V hU hV hf hf' h hfD hf'D
  have hx' : x ∈ Φ.source := by rw [hsrc]; exact hx
  rw [← hfu]
  exact PartialDiffeomorph.isLocalDiffeomorphAt I J n Φ hx'

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G} [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}
/--
[odm_isLocalDiffeomorphAt_congr_of_eventuallyEq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
Proved via the double local inverse: the local inverse of the local inverse is a
smooth twin of the original map, so the new map inherits smooth inverse data. -/
private lemma odm_isLocalDiffeomorphAt_congr_of_eventuallyEq
  {f f₂ : M → N} {x : M}
  (hf : IsLocalDiffeomorphAt I J n f x) (h : f₂ =ᶠ[nhds x] f) :
  IsLocalDiffeomorphAt I J n f₂ x := by
  set g : N → M := ⇑hf.localInverse with hgdef
  have hg : IsLocalDiffeomorphAt J I n g (f x) := hf.localInverse_isLocalDiffeomorphAt
  set g₂ : M → N := ⇑hg.localInverse with hg₂def
  have e1 : g ∘ f =ᶠ[nhds x] id := hf.localInverse_eventuallyEq_left
  have e2 : g₂ ∘ g =ᶠ[nhds (f x)] id := hg.localInverse_eventuallyEq_left
  have hcont : ContinuousAt f x := hf.contMDiffAt.continuousAt
  have key : g₂ =ᶠ[nhds x] f := by
    have A : g₂ ∘ (g ∘ f) =ᶠ[nhds x] g₂ ∘ id :=
      e1.mono fun z hz => congrArg g₂ hz
    have B : (g₂ ∘ g) ∘ f =ᶠ[nhds x] id ∘ f := hcont.eventually e2
    have A' : (g₂ ∘ g) ∘ f =ᶠ[nhds x] g₂ := by
      rwa [← Function.comp_assoc, Function.comp_id] at A
    have B' : (g₂ ∘ g) ∘ f =ᶠ[nhds x] f := by simpa using B
    exact A'.symm.trans B'
  have hfg : f₂ =ᶠ[nhds x] g₂ := h.trans key.symm
  have hUmem : { z | f₂ z = g₂ z } ∈ nhds x := hfg
  obtain ⟨U₀, hU₀sub, hU₀open, hU₀x⟩ := mem_nhds_iff.mp hUmem
  have hxg₂ : x ∈ hg.localInverse.source := by
    have h1 : g (f x) ∈ hg.localInverse.source := hg.localInverse_mem_source
    have h2 : g (f x) = x :=
      hf.localInverse_left_inv hf.localInverse_mem_target
    rwa [h2] at h1
  set W : Set M := U₀ ∩ hg.localInverse.source with hWdef
  have hxW : x ∈ W := ⟨hU₀x, hxg₂⟩
  have hWopen : IsOpen W := hU₀open.inter hg.localInverse.open_source
  have hWsub : W ⊆ hg.localInverse.source := Set.inter_subset_right
  have heqW : Set.EqOn f₂ g₂ W := fun z hz => hU₀sub hz.1
  have hf₂D : ContMDiffOn I J n f₂ W :=
    (hg.localInverse.contMDiffOn_toFun.mono hWsub).congr (fun z hz => heqW hz)
  set V : Set N :=
    hg.localInverse.symm.source ∩ ⇑hg.localInverse.symm ⁻¹' W with hVdef
  have hVopen : IsOpen V :=
    hg.localInverse.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      hg.localInverse.symm.open_source hWopen
  have hVsub : V ⊆ hg.localInverse.target := fun w hw => hw.1
  have hVL : Set.MapsTo f₂ W V := by
    intro z hz
    have hzT : hg.localInverse z ∈ hg.localInverse.target :=
      hg.localInverse.toPartialEquiv.map_source (hWsub hz)
    have hzeq : f₂ z = hg.localInverse z := heqW hz
    refine ⟨?_, ?_⟩
    · rw [hzeq]; exact hzT
    · change hg.localInverse.symm (f₂ z) ∈ W
      have hleft : hg.localInverse.symm (hg.localInverse z) = z :=
        hg.localInverse.toPartialEquiv.left_inv (hWsub hz)
      rw [hzeq]
      rwa [hleft]
  have hVR : Set.MapsTo hg.localInverse.symm V W := fun w hw => hw.2
  have hInv : Set.InvOn hg.localInverse.symm f₂ W V := by
    constructor
    · intro z hz
      show hg.localInverse.symm (f₂ z) = z
      have hzeq : f₂ z = hg.localInverse z := heqW hz
      rw [hzeq]
      exact hg.localInverse.toPartialEquiv.left_inv (hWsub hz)
    · intro w hw
      have hwW : hg.localInverse.symm w ∈ W := hw.2
      calc f₂ (hg.localInverse.symm w) = hg.localInverse (hg.localInverse.symm w) :=
        heqW hwW
        _ = w := hg.localInverse.toPartialEquiv.right_inv (hVsub hw)
  have hf'D : ContMDiffOn J I n hg.localInverse.symm V :=
    hg.localInverse.symm.contMDiffOn_toFun.mono (fun w hw => hw.1)
  exact odm_isLocalDiffeomorphAt_of_invOn f₂ hg.localInverse.symm W V hWopen hVopen
    hVL hVR hInv hf₂D hf'D x hxW

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

/--
[odm_exists_contDiff_deriv_pos_range_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
everywhere positive derivative. -/
private lemma odm_exists_contDiff_deriv_pos_range_eq
  (D : Set ℝ) (hDopen : IsOpen D) (hDconn : D.OrdConnected) (hDne : D.Nonempty) :
  ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ t, 0 < deriv φ t) ∧ Set.range φ = D := by
  have hpre : IsPreconnected D := hDconn.isPreconnected
  have hex_lt : ∀ a : ℝ, a ∈ D → ∃ q ∈ D, q < a := by
    intro a ha
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hDopen.mem_nhds ha)
    refine ⟨a - ε / 2, hball ?_, by linarith⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have he : (a - ε / 2) - a = -(ε / 2) := by ring
    rw [he, norm_neg, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
    linarith
  have hex_gt : ∀ b : ℝ, b ∈ D → ∃ q ∈ D, b < q := by
    intro b hb
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hDopen.mem_nhds hb)
    refine ⟨b + ε / 2, hball ?_, by linarith⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have he : (b + ε / 2) - b = ε / 2 := by ring
    rw [he, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
    linarith
  set a : ℝ := sInf D with ha
  set b : ℝ := sSup D with hb
  obtain h | h | h | h | h | h | h | h | h | h := hpre.mem_intervals
  · -- D = Icc: left endpoint contradicts openness.
    rw [← ha, ← hb] at h
    obtain ⟨x, hx⟩ := hDne
    rw [h] at hx
    have hab : a ≤ b :=
      (Set.mem_Icc.mp hx).1.trans (Set.mem_Icc.mp hx).2
    have haD : a ∈ D := by
      rw [h]
      exact Set.mem_Icc.mpr ⟨le_rfl, hab⟩
    obtain ⟨q, hqD, hqa⟩ := hex_lt _ haD
    rw [h] at hqD
    exact absurd (Set.mem_Icc.mp hqD).1 (not_le.mpr hqa)
  · -- D = Ico: left endpoint contradicts openness.
    rw [← ha, ← hb] at h
    obtain ⟨x, hx⟩ := hDne
    rw [h] at hx
    have hab : a < b :=
      (Set.mem_Ico.mp hx).1.trans_lt (Set.mem_Ico.mp hx).2
    have haD : a ∈ D := by
      rw [h]
      exact Set.mem_Ico.mpr ⟨le_rfl, hab⟩
    obtain ⟨q, hqD, hqa⟩ := hex_lt _ haD
    rw [h] at hqD
    exact absurd (Set.mem_Ico.mp hqD).1 (not_le.mpr hqa)
  · -- D = Ioc: right endpoint contradicts openness.
    rw [← ha, ← hb] at h
    obtain ⟨x, hx⟩ := hDne
    rw [h] at hx
    have hab : a < b :=
      (Set.mem_Ioc.mp hx).1.trans_le (Set.mem_Ioc.mp hx).2
    have hbD : b ∈ D := by
      rw [h]
      exact Set.mem_Ioc.mpr ⟨hab, le_rfl⟩
    obtain ⟨q, hqD, hqb⟩ := hex_gt _ hbD
    rw [h] at hqD
    exact absurd (Set.mem_Ioc.mp hqD).2 (not_le.mpr hqb)
  · -- D = Ioo: arctan parametrisation.
    rw [← ha, ← hb] at h
    obtain ⟨x, hx⟩ := hDne
    rw [h] at hx
    have hab : a < b :=
      lt_trans (Set.mem_Ioo.mp hx).1 (Set.mem_Ioo.mp hx).2
    set k : ℝ := (b - a) / Real.pi with hk
    have hkpos : 0 < k := by
      rw [hk]
      exact div_pos (by linarith) Real.pi_pos
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hk2 : k * (Real.pi / 2) = (b - a) / 2 := by
      rw [hk]
      field_simp
    refine ⟨fun t => (a + b) / 2 + k * Real.arctan t, ?_, ?_, ?_⟩
    · exact contDiff_const.add (contDiff_const.mul Real.contDiff_arctan)
    · intro t
      have hder : deriv (fun t => (a + b) / 2 + k * Real.arctan t) t
        = k * (1 / (1 + t ^ 2)) :=
        (((Real.hasDerivAt_arctan t).const_mul k).const_add _).deriv
      rw [hder]
      exact mul_pos hkpos (by positivity)
    · rw [h]
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        have hart : Real.arctan t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
          rw [← Real.range_arctan]
          exact Set.mem_range_self t
        rw [Set.mem_Ioo] at hart ⊢
        have lo := mul_lt_mul_of_pos_left hart.1 hkpos
        have hi := mul_lt_mul_of_pos_left hart.2 hkpos
        constructor <;> nlinarith [hk2]
      · intro hy
        rw [Set.mem_Ioo] at hy
        have hs : (y - (a + b) / 2) / k ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
          rw [Set.mem_Ioo]
          constructor
          · rw [lt_div_iff₀ hkpos]
            nlinarith [hy.1, hk2]
          · rw [div_lt_iff₀ hkpos]
            nlinarith [hy.2, hk2]
        rw [← Real.range_arctan] at hs
        obtain ⟨t, ht⟩ := hs
        refine ⟨t, ?_⟩
        have hkne : k ≠ 0 := hkpos.ne'
        change (a + b) / 2 + k * Real.arctan t = y
        rw [ht]
        field_simp
        ring
  · -- D = Ici: left endpoint contradicts openness.
    rw [← ha] at h
    have haD : a ∈ D := by
      rw [h]
      exact Set.mem_Ici.mpr le_rfl
    obtain ⟨q, hqD, hqa⟩ := hex_lt _ haD
    rw [h] at hqD
    exact absurd (Set.mem_Ici.mp hqD) (not_le.mpr hqa)
  · -- D = Ioi: exp parametrisation.
    rw [← ha] at h
    refine ⟨fun t => a + Real.exp t, contDiff_const.add Real.contDiff_exp, ?_, ?_⟩
    · intro t
      have hder : deriv (fun t => a + Real.exp t) t = Real.exp t :=
        ((Real.hasDerivAt_exp t).const_add a).deriv
      rw [hder]
      exact Real.exp_pos t
    · rw [h]
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        refine Set.mem_Ioi.mpr ?_
        change a < a + Real.exp t
        have hpos := Real.exp_pos t
        linarith
      · intro hy
        rw [Set.mem_Ioi] at hy
        have hmem : y - a ∈ Set.range Real.exp := by
          rw [Real.range_exp]
          exact Set.mem_Ioi.mpr (by linarith)
        obtain ⟨t, ht⟩ := hmem
        refine ⟨t, ?_⟩
        change a + Real.exp t = y
        rw [ht]
        ring
  · -- D = Iic: right endpoint contradicts openness.
    rw [← hb] at h
    have hbD : b ∈ D := by
      rw [h]
      exact Set.mem_Iic.mpr le_rfl
    obtain ⟨q, hqD, hqb⟩ := hex_gt _ hbD
    rw [h] at hqD
    exact absurd (Set.mem_Iic.mp hqD) (not_le.mpr hqb)
  · -- D = Iio: reflected exp parametrisation.
    rw [← hb] at h
    refine ⟨fun t => b - Real.exp (-t),
      contDiff_const.sub (Real.contDiff_exp.comp contDiff_id.neg), ?_, ?_⟩
    · intro t
      have h1 : HasDerivAt (fun t : ℝ => -t) (-1) t := (hasDerivAt_id t).neg
      have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-t) * -1) t :=
        h1.exp
      have h3 := h2.const_sub b
      have hder : deriv (fun t => b - Real.exp (-t)) t = Real.exp (-t) := by
        have hderiv := h3.deriv
        simpa using hderiv
      rw [hder]
      exact Real.exp_pos _
    · rw [h]
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        refine Set.mem_Iio.mpr ?_
        change b - Real.exp (-t) < b
        have hpos := Real.exp_pos (-t)
        linarith
      · intro hy
        rw [Set.mem_Iio] at hy
        have hpos : (0 : ℝ) < b - y := by linarith
        refine ⟨-(Real.log (b - y)), ?_⟩
        have hexp : Real.exp (-(-(Real.log (b - y)))) = b - y := by
          rw [neg_neg, Real.exp_log hpos]
        change b - Real.exp (-(-(Real.log (b - y)))) = y
        rw [hexp]
        ring
  · -- D = univ: identity.
    rw [h]
    exact ⟨id, contDiff_id,
      fun t => by rw [(hasDerivAt_id t).deriv]; exact one_pos, Set.range_id⟩
  · -- D = ∅ contradicts nonemptiness.
    obtain ⟨x, hx⟩ := hDne
    rw [h] at hx
    exact absurd hx (Set.notMem_empty x)

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

/--
[odm_exists_partialDiffeomorph_of_deriv_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
with everywhere positive derivative on an open connected set is a diffeomorphism onto
its image, with explicit inverse derivative. -/
private theorem odm_exists_partialDiffeomorph_of_deriv_pos
  (J : Set ℝ) (f : ℝ → ℝ) (hJopen : IsOpen J) (hJconn : J.OrdConnected)
  (hfd : ContDiffOn ℝ ∞ f J) (hderiv : ∀ t ∈ J, 0 < deriv f t) :
  ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞, Φ.source = J ∧
    (⇑Φ : ℝ → ℝ) = f ∧ Φ.target = f '' J ∧ (Φ.target).OrdConnected ∧
    ∀ u ∈ Φ.target, HasDerivAt ⇑Φ.symm ((deriv f (Φ.symm u))⁻¹) u := by
  have hcont : ContinuousOn f J := hfd.continuousOn
  have hstrict : StrictMonoOn f J :=
    strictMonoOn_of_deriv_pos hJconn.convex hcont (by
      rw [hJopen.interior_eq]
      exact hderiv)
  have hinj : Set.InjOn f J := hstrict.injOn
  let e : PartialEquiv ℝ ℝ := hinj.toPartialEquiv f J
  have hne : ∀ t ∈ J, deriv f t ≠ 0 := fun t ht => (hderiv t ht).ne'
  have hsd : ∀ t ∈ J, HasStrictDerivAt f (deriv f t) t := by
    intro t ht
    exact ((hfd.contDiffAt (hJopen.mem_nhds ht)).hasStrictDerivAt (by simp))
  have hmap : ∀ t ∈ J, Filter.map f (𝓝 t) = 𝓝 (f t) := by
    intro t ht
    exact HasStrictDerivAt.map_nhds_eq (hsd t ht) (hne t ht)
  have himg : ∀ V : Set ℝ, IsOpen V → IsOpen (f '' (V ∩ J)) := by
    intro V hV
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨t, ⟨htV, htJ⟩, rfl⟩
    have hmem : V ∩ J ∈ 𝓝 t :=
      Filter.inter_mem (hV.mem_nhds htV) (hJopen.mem_nhds htJ)
    exact (hmap t htJ) ▸ Filter.image_mem_map hmem
  have htgt : IsOpen (f '' J) := by
    have hU := himg Set.univ isOpen_univ
    rwa [Set.univ_inter] at hU
  have hsymm : ∀ t ∈ J, HasStrictDerivAt ⇑e.symm ((deriv f t)⁻¹) (f t) := by
    intro t ht
    exact HasStrictDerivAt.to_local_left_inverse (hsd t ht) (hne t ht)
      (Filter.eventually_of_mem (hJopen.mem_nhds ht) (fun x hx => e.left_inv hx))
  have hcont_inv : ContinuousOn ⇑e.symm (f '' J) := by
    intro u hu
    obtain ⟨t, htJ, rfl⟩ := hu
    exact ((hsymm t htJ).hasDerivAt.continuousAt).continuousWithinAt
  let o : OpenPartialHomeomorph ℝ ℝ :=
    OpenPartialHomeomorph.mk (PartialHomeomorph.mk e hcont hcont_inv) hJopen htgt
  have ho_src : o.source = J := rfl
  have ho_tgt : o.target = f '' J := rfl
  have hst : ∀ s ∈ J, o.symm (f s) = s := fun s hs => e.left_inv hs
  have hmem_src : ∀ s ∈ J, s ∈ o.source := fun s hs => hs
  have hCdAt : ∀ x ∈ o.target, ContDiffAt ℝ ∞ ⇑o.symm x := by
    intro x hx
    have hxJ : x ∈ f '' J := hx
    obtain ⟨t, htJ, rfl⟩ := hxJ
    have hsymm_eq : o.symm (f t) = t := hst t htJ
    have hmem_t : f t ∈ o.target := by
      have hmem : f t ∈ f '' J := Set.mem_image_of_mem f htJ
      exact hmem
    have hmemJ : o.symm (f t) ∈ J := by
      rwa [hsymm_eq]
    have hf₀' : HasDerivAt ⇑o (deriv f (o.symm (f t))) (o.symm (f t)) :=
      (hsd _ hmemJ).hasDerivAt
    have hfC : ContDiffAt ℝ ∞ ⇑o (o.symm (f t)) :=
      hfd.contDiffAt (hJopen.mem_nhds hmemJ)
    have h₀ : deriv f (o.symm (f t)) ≠ 0 := by
      rw [hsymm_eq]
      exact hne t htJ
    exact o.contDiffAt_symm_deriv h₀ hmem_t hf₀' hfC
  have hsymmD : ContDiffOn ℝ ∞ ⇑e.symm e.target := by
    intro x hx
    have hxJ : x ∈ o.target := hx
    have hCd : ContDiffAt ℝ ∞ ⇑e.symm x := hCdAt x hxJ
    exact (contDiffWithinAt_univ.mpr hCd).mono (Set.subset_univ _)
  have hfDtoFun : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ⇑e e.source :=
    contMDiffOn_iff_contDiffOn.mpr (by exact hfd)
  have hfDinvFun : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ⇑e.symm e.target :=
    contMDiffOn_iff_contDiffOn.mpr hsymmD
  have hpre : IsPreconnected (f '' J) := hJconn.isPreconnected.image f hcont
  have hord : (f '' J).OrdConnected := isPreconnected_iff_ordConnected.mp hpre
  have hsymm_deriv : ∀ u ∈ e.target,
    HasDerivAt ⇑e.symm ((deriv f (⇑e.symm u))⁻¹) u := by
    intro u hu
    have huJ : u ∈ f '' J := hu
    obtain ⟨t, htJ, rfl⟩ := huJ
    have h1 : ⇑e.symm (f t) = t := e.left_inv htJ
    rw [h1]
    exact (hsymm t htJ).hasDerivAt
  refine ⟨PartialDiffeomorph.mk e hJopen htgt hfDtoFun hfDinvFun,
    rfl, rfl, rfl, hord, ?_⟩
  intro u hu
  exact hsymm_deriv u hu
section SpeedSetup
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M]

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
/--
[om_riemannianMetric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma om_riemannianMetric [T2Space M] [SecondCountableTopology M] :
  Nonempty (Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x)) :=
  MathlibExt.Geometry.Manifold.RiemannianMetricExistenceWanted.riemannianMetricExistence

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
/--
[om_contDiffOn_curveSpeedSq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma om_contDiffOn_curveSpeedSq
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
  (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ U) :
  ContDiffOn ℝ ∞ (fun t => omCurveSpeedSq g γ t) U := by
  let hRiem : Bundle.RiemannianBundle (fun x : M => TangentSpace (𝓡 1) x) :=
    ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x) :=
    ⟨g.inner, g.contMDiff, fun x v w => rfl⟩
  have hagree : ∀ (x : M) (v w : TangentSpace (𝓡 1) x),
    inner ℝ v w = g.inner x v w := fun x v w => rfl
  have htm := ContMDiffOn.contMDiffOn_tangentMapWithin hγ (m := ∞) (by simp)
    hU.uniqueMDiffOn
  have h1id : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => s) := contMDiff_id
  have h1c : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun _ : ℝ => (1 : ℝ)) := contMDiff_const
  have hpair : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞ omPairFn := by
    unfold omPairFn
    convert ContMDiff.prodMk h1id h1c using 2
    · rfl
    · rfl
    · exact chartedSpaceSelf_prod.symm
  have hsymmP : ContMDiff 𝓘(ℝ, ℝ).tangent 𝓘(ℝ, ℝ).tangent ∞
    ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
      ℝ × ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
    contMDiff_tangentBundleModelSpaceHomeomorph_symm
  have hfac : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
    ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm ∘ omPairFn)
    U :=
    (ContMDiff.contMDiffOn (ContMDiff.comp hsymmP hpair))
  have hproj : ∀ s : ℝ, Bundle.TotalSpace.proj
    ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm (s, (1 : ℝ))) = s :=
    fun s => rfl
  have hpt : ∀ s : ℝ, (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm (s, (1 : ℝ))
    = (⟨s, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) := fun s => rfl
  have hmaps : Set.MapsTo
    ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm ∘ omPairFn)
    U (Bundle.TotalSpace.proj ⁻¹' U) := by
    intro s hs
    simp only [Set.mem_preimage, Function.comp_apply, omPairFn]
    rwa [hproj]
  have hW := ContMDiffOn.comp htm hfac hmaps
  have hsec : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1).tangent ∞
    (fun t : ℝ => ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ) : TangentSpace (𝓡 1) (γ t)) :
      TangentBundle (𝓡 1) M)) U := by
    apply ContMDiffOn.congr hW
    intro t ht
    change ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ) : TangentSpace (𝓡 1) (γ t)) :
      TangentBundle (𝓡 1) M)
      = tangentMapWithin 𝓘(ℝ, ℝ) (𝓡 1) γ U
        ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm (t, (1 : ℝ)))
    rw [hpt]
    change ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ) : TangentSpace (𝓡 1) (γ t)) :
      TangentBundle (𝓡 1) M)
      = (⟨γ t, mfderivWithin 𝓘(ℝ, ℝ) (𝓡 1) γ U t (1 : ℝ)⟩ :
        TangentBundle (𝓡 1) M)
    rw [mfderivWithin_of_isOpen hU ht]
  have hinner : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
    (fun t : ℝ => inner ℝ (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))) U :=
    ContMDiffOn.inner_bundle hsec hsec
  have hdiff : ContDiffOn ℝ ∞
    (fun t : ℝ => inner ℝ (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))) U :=
    contMDiffOn_iff_contDiffOn.mp hinner
  apply ContDiffOn.congr hdiff
  intro t _
  show omCurveSpeedSq g γ t = _
  unfold omCurveSpeedSq
  exact (hagree _ _ _).symm

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
/--
[om_curveSpeedSq_eq_of_eventuallyEq_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
speed of `β`. -/
private lemma om_curveSpeedSq_eq_of_eventuallyEq_comp
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (β : ℝ → M) (k : ℝ → ℝ) (t : ℝ)
  (hk : DifferentiableAt ℝ k t)
  (hβ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) β (k t))
  {γ : ℝ → M} (hγ : γ =ᶠ[nhds t] β ∘ k) :
  omCurveSpeedSq g γ t = (deriv k t) ^ 2 * omCurveSpeedSq g β (k t) := by
  have hk' : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k t :=
    DifferentiableAt.mdifferentiableAt hk
  have hβk : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) (β ∘ k) t :=
    MDifferentiableAt.comp t hβ hk'
  have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) γ t :=
    MDifferentiableAt.congr_of_eventuallyEq hβk hγ
  have H : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 1) (β ∘ k) t
    ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t)).comp (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k t)) :=
    HasMFDerivAt.comp t (MDifferentiableAt.hasMFDerivAt hβ)
      (MDifferentiableAt.hasMFDerivAt hk')
  have Hγ : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 1) γ t
    ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t)).comp (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k t)) :=
    HasMFDerivAt.congr_of_eventuallyEq_abuse H hγ
  have hmeq : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t
    = mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (β ∘ k) t :=
    (HasMFDerivAt.mfderiv Hγ).trans (HasMFDerivAt.mfderiv H).symm
  have hpt : γ t = β (k t) := Filter.EventuallyEq.eq_of_nhds hγ
  have hk1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k t (1 : ℝ) = deriv k t :=
    Eq.trans
      (congrArg (fun D : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) t =>
        D (1 : ℝ)) mfderiv_eq_fderiv)
      (Eq.trans (show (fderiv ℝ k t) (1 : ℝ) = (1 : ℝ) • deriv k t from
        fderiv_eq_smul_deriv _) (one_smul _ _))
  have hcomp : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (β ∘ k) t (1 : ℝ)
    = mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k t (1 : ℝ)) :=
    mfderiv_comp_apply t hβ hk' ((1 : ℝ))
  have hmf1 : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ)
    = mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (deriv k t) :=
    Eq.trans
      (congrArg (fun D : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] EuclideanSpace ℝ (Fin 1) =>
        D (1 : ℝ)) hmeq)
      (Eq.trans hcomp
        (congrArg (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t)) hk1))
  have hsc : (deriv k t : ℝ) = (deriv k t) • (1 : ℝ) := by
    rw [smul_eq_mul, mul_one]
  have hmf1c : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ)
    = mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) ((deriv k t) • (1 : ℝ)) :=
    hmf1.trans (congrArg (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t)) hsc)
  change g.inner (γ t) _ _ = _
  rw [hpt]
  have eA : g.inner (β (k t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
    = g.inner (β (k t))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) ((deriv k t) • (1 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) ((deriv k t) • (1 : ℝ))) :=
    congrArg (fun v => g.inner (β (k t)) v v) hmf1c
  have m1 : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) ((deriv k t) • (1 : ℝ))
    = (deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ) :=
    map_smul (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t)) (deriv k t) (1 : ℝ)
  have eB : g.inner (β (k t))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) ((deriv k t) • (1 : ℝ)))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) ((deriv k t) • (1 : ℝ)))
    = g.inner (β (k t))
      ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
      ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)) :=
    congrArg (fun v => g.inner (β (k t)) v v) m1
  have e_i1 : (g.inner (β (k t)))
    ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
    = (deriv k t) • ((g.inner (β (k t)))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))) :=
    map_smul (g.inner (β (k t))) (deriv k t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
  have e_ii : g.inner (β (k t))
    ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
    ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
    = ((deriv k t) • ((g.inner (β (k t)))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))))
      ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)) :=
    congrArg (fun w : TangentSpace (𝓡 1) (β (k t)) →L[ℝ] ℝ =>
      w ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))) e_i1
  have e_iii : ((deriv k t) • ((g.inner (β (k t)))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))))
    ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
    = (deriv k t) • ((((deriv k t) • ((g.inner (β (k t)))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)))))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))) :=
    map_smul (((deriv k t) • ((g.inner (β (k t)))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))))) (deriv k t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
  have e_iv : ((((deriv k t) • ((g.inner (β (k t)))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)))))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)))
    = (deriv k t) • ((((g.inner (β (k t)))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))) :=
    rfl
  have m2 : g.inner (β (k t))
    ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
    ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
    = (deriv k t) • ((deriv k t) •
      g.inner (β (k t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))) :=
    e_ii.trans (e_iii.trans (congrArg ((deriv k t) • ·) e_iv))
  have s1 : (deriv k t) • ((deriv k t) •
    g.inner (β (k t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)))
    = (deriv k t) ^ 2 *
      g.inner (β (k t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)) := by
    simp only [smul_eq_mul, pow_two]
    ring
  have eC : g.inner (β (k t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
    = (deriv k t) ^ 2 *
      g.inner (β (k t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)) :=
    eA.trans (eB.trans (m2.trans s1))
  unfold omCurveSpeedSq
  exact eC

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
/--
[om_curveSpeedSq_pos_of_partialDiffeomorph](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma om_curveSpeedSq_pos_of_partialDiffeomorph
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞) {s : ℝ} (hs : s ∈ Φ.source) :
  0 < omCurveSpeedSq g Φ s := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hΦ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) ⇑Φ s := Φ.mdifferentiableAt hn hs
  have hΦs : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) ⇑Φ.symm (Φ s) :=
    Φ.symm.mdifferentiableAt hn (Φ.map_source hs)
  apply g.pos
  intro h0
  have hev : (fun y => Φ.symm (Φ y)) =ᶠ[nhds s] id :=
    Filter.eventually_of_mem (Φ.open_source.mem_nhds hs)
      (fun y hy => Φ.toPartialEquiv.left_inv hy)
  have e1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (⇑Φ.symm ∘ ⇑Φ) s
    = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id s :=
    HasMFDerivAt.mfderiv (HasMFDerivAt.congr_of_eventuallyEq_abuse
      (MDifferentiableAt.hasMFDerivAt mdifferentiableAt_id) hev)
  have e2 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (⇑Φ.symm ∘ ⇑Φ) s (1 : ℝ)
    = mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ⇑Φ.symm (Φ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) ⇑Φ s (1 : ℝ)) :=
    mfderiv_comp_apply s hΦs hΦ ((1 : ℝ))
  have e3 : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ⇑Φ.symm (Φ s)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) ⇑Φ s (1 : ℝ))
    = mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ⇑Φ.symm (Φ s) 0 :=
    congrArg (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ⇑Φ.symm (Φ s)) h0
  have e4 : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ⇑Φ.symm (Φ s) 0 = (0 : ℝ) :=
    map_zero (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ⇑Φ.symm (Φ s))
  have e5 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id s (1 : ℝ) = (1 : ℝ) :=
    Eq.trans
      (congrArg (fun D : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) s =>
        D (1 : ℝ)) mfderiv_id)
      rfl
  have e6 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (⇑Φ.symm ∘ ⇑Φ) s (1 : ℝ) = (0 : ℝ) :=
    e2.trans (e3.trans e4)
  have e7 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (⇑Φ.symm ∘ ⇑Φ) s (1 : ℝ) = (1 : ℝ) :=
    congrArg (fun D : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) s =>
      D (1 : ℝ)) e1 |>.trans e5
  have e8 : (1 : ℝ) = (0 : ℝ) := e7.symm.trans e6
  exact one_ne_zero e8

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

/--
[om_arclength_contDiffOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
containing `0` is smooth, with the expected derivative. -/
private lemma om_arclength_contDiffOn
  (I : Set ℝ) (σ : ℝ → ℝ) (hIopen : IsOpen I) (hIconn : I.OrdConnected)
  (h0 : (0 : ℝ) ∈ I)
  (hσ : ContDiffOn ℝ ∞ σ I) (hpos : ∀ s ∈ I, 0 < σ s) :
  ContDiffOn ℝ ∞
    (fun s => intervalIntegral (fun u => Real.sqrt (σ u)) 0 s MeasureTheory.volume) I ∧
    (∀ s ∈ I, HasDerivAt
      (fun t => intervalIntegral (fun u => Real.sqrt (σ u)) 0 t MeasureTheory.volume)
      (Real.sqrt (σ s)) s) := by
  have hsqrt : ContDiffOn ℝ ∞ (fun s => Real.sqrt (σ s)) I :=
    hσ.sqrt (fun s hs => ne_of_gt (hpos s hs))
  have hcont : ContinuousOn (fun s => Real.sqrt (σ s)) I := hsqrt.continuousOn
  have hsub : ∀ s ∈ I, Set.uIcc (0 : ℝ) s ⊆ I :=
    fun s hs => hIconn.uIcc_subset h0 hs
  have hder : ∀ s ∈ I, HasDerivAt
    (fun t => intervalIntegral (fun u => Real.sqrt (σ u)) 0 t MeasureTheory.volume)
    (Real.sqrt (σ s)) s := by
    intro s hs
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (hcont.mono (hsub s hs)).intervalIntegrable
    · exact ContinuousAt.stronglyMeasurableAtFilter hIopen
      (fun x hx => hcont.continuousAt (hIopen.mem_nhds hx)) s hs
    · exact hcont.continuousAt (hIopen.mem_nhds hs)
  have hdiff : DifferentiableOn ℝ
    (fun t => intervalIntegral (fun u => Real.sqrt (σ u)) 0 t MeasureTheory.volume) I :=
    fun s hs => (hder s hs).differentiableAt.differentiableWithinAt
  have hderiv_smooth : ContDiffOn ℝ ∞
    (deriv (fun t => intervalIntegral (fun u => Real.sqrt (σ u)) 0 t MeasureTheory.volume)) I :=
    hsqrt.congr (fun s hs => (hder s hs).deriv)
  exact ⟨(contDiffOn_infty_iff_deriv_of_isOpen hIopen).mpr ⟨hdiff, hderiv_smooth⟩, hder⟩
section UnitSpeedCharts
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M]

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
/--
[om_chartInverse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
neighbourhood of `x`, with positive smooth speed. -/
private lemma om_chartInverse
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (x : M) :
  ∃ β0 : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞,
    β0.source.OrdConnected ∧ (0 : ℝ) ∈ β0.source ∧ β0 0 = x ∧
      (∀ s ∈ β0.source, 0 < omCurveSpeedSq g β0 s) ∧
      ContDiffOn ℝ ∞ (fun s => omCurveSpeedSq g β0 s) β0.source := by
  set e := omLinEquiv with he
  set ch := chartAt (EuclideanSpace ℝ (Fin 1)) x with hch
  set x' := ch x with hx'
  have hx'src : x ∈ ch.source :=
    mem_chart_source (EuclideanSpace ℝ (Fin 1)) x
  have hx'tgt : x' ∈ ch.target :=
    mem_chart_target (EuclideanSpace ℝ (Fin 1)) x
  have hVopen : IsOpen ((fun s : ℝ => x' + e s) ⁻¹' ch.target) :=
    ch.open_target.preimage (continuous_const.add e.continuous)
  have hV0 : (0 : ℝ) ∈ (fun s : ℝ => x' + e s) ⁻¹' ch.target := by
    have h0e : x' + e (0 : ℝ) = x' := by simp
    simpa [h0e] using hx'tgt
  obtain ⟨r, hrpos, hball⟩ := Metric.isOpen_iff.mp hVopen 0 hV0
  set I0 : Set ℝ := Set.Ioo (-r) r with hI0
  have hI0sub : I0 ⊆ (fun s : ℝ => x' + e s) ⁻¹' ch.target := by
    intro s hs
    rw [hI0] at hs
    have hmem : s ∈ Metric.ball (0 : ℝ) r := by
      rw [Real.ball_eq_Ioo]
      simpa using hs
    exact hball hmem
  have hI0open : IsOpen I0 := isOpen_Ioo
  have hI0conn : I0.OrdConnected :=
    isPreconnected_iff_ordConnected.mp isPreconnected_Ioo
  have hI00 : (0 : ℝ) ∈ I0 := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  set W : Set (EuclideanSpace ℝ (Fin 1)) :=
    (fun v : EuclideanSpace ℝ (Fin 1) => e.symm (v - x')) ⁻¹' I0 with hW
  have hWopen : IsOpen W :=
    hI0open.preimage (e.symm.continuous.comp (continuous_id.sub continuous_const))
  set V : Set M := ch.source ∩ ⇑ch ⁻¹' W with hV
  have hVopen : IsOpen V :=
    ch.continuousOn.isOpen_inter_preimage ch.open_source hWopen
  set f : ℝ → M := fun s => ch.symm (x' + e s) with hf
  set f' : M → ℝ := fun y => e.symm (ch y - x') with hf'
  have hleft : ∀ s ∈ I0, f' (f s) = s := by
    intro s hs
    have hmem : x' + e s ∈ ch.target := hI0sub hs
    change e.symm (ch (ch.symm (x' + e s)) - x') = s
    rw [ch.right_inv hmem]
    have hab : x' + e s - x' = e s := by abel
    rw [hab]
    simp
  have hright : ∀ y ∈ V, f (f' y) = y := by
    intro y hy
    obtain ⟨hysrc, -⟩ := hy
    change ch.symm (x' + e (e.symm (ch y - x'))) = y
    have h1 : e (e.symm (ch y - x')) = ch y - x' := by simp
    rw [h1]
    have h2 : x' + (ch y - x') = ch y := by abel
    rw [h2]
    exact ch.left_inv hysrc
  have hfmaps : Set.MapsTo f I0 V := by
    intro s hs
    constructor
    · exact ch.map_target (hI0sub hs)
    · change ch (f s) ∈ W
      have hmem : x' + e s ∈ ch.target := hI0sub hs
      have hchf : ch (f s) = x' + e s := ch.right_inv hmem
      change (fun v : EuclideanSpace ℝ (Fin 1) => e.symm (v - x')) (ch (f s)) ∈ I0
      rw [hchf]
      change e.symm (x' + e s - x') ∈ I0
      have hab : x' + e s - x' = e s := by abel
      rw [hab]
      simpa using hs
  have hf'maps : Set.MapsTo f' V I0 := by
    intro y hy
    obtain ⟨-, hyW⟩ := hy
    change e.symm (ch y - x') ∈ I0
    change (fun v : EuclideanSpace ℝ (Fin 1) => e.symm (v - x')) (ch y) ∈ I0
    exact hyW
  have haff : ContDiff ℝ ∞ (fun s : ℝ => x' + e s) :=
    contDiff_const.add e.contDiff
  have haffM : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ (fun s : ℝ => x' + e s) I0 :=
    ((haff.contMDiff).contMDiffOn.mono (Set.subset_univ I0))
  have hfD : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ f I0 :=
    ((contMDiffOn_chart_symm (x := x) :
      ContMDiffOn (𝓡 1) (𝓡 1) ∞ ⇑ch.symm ch.target).comp haffM
      (fun s hs => hI0sub hs))
  have hsub' : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 1) => e.symm (v - x')) :=
    e.symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have houter : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞
    (⇑e.symm ∘ fun v : EuclideanSpace ℝ (Fin 1) => v - x') Set.univ :=
    (hsub'.contMDiff).contMDiffOn
  have hf'D : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ f' V :=
    houter.comp (contMDiffOn_chart.mono Set.inter_subset_left)
      (Set.mapsTo_univ _ _)
  obtain ⟨β0, hβsrc, hβtgt, hβfun, -⟩ :=
    odm_exists_partialDiffeomorph_of_invOn f f' I0 V hI0open hVopen
      hfmaps hf'maps ⟨hleft, hright⟩ hfD hf'D
  refine ⟨β0, hβsrc.symm ▸ hI0conn, hβsrc.symm ▸ hI00, ?_, ?_, ?_⟩
  · rw [hβfun]
    change ch.symm (x' + e (0 : ℝ)) = x
    have h0e : x' + e (0 : ℝ) = x' := by simp
    rw [h0e]
    exact ch.left_inv hx'src
  · intro s hs
    exact om_curveSpeedSq_pos_of_partialDiffeomorph g β0 hs
  · exact om_contDiffOn_curveSpeedSq g ⇑β0 β0.source β0.open_source
    β0.contMDiffOn_toFun

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
/--
[om_exists_unitSpeedChart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma om_exists_unitSpeedChart
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (x : M) :
  ∃ α : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞,
    α.source.OrdConnected ∧ (0 : ℝ) ∈ α.source ∧ α 0 = x ∧
      ∀ s ∈ α.source, omCurveSpeedSq g α s = 1 := by
  obtain ⟨β0, hβconn, hβ0, hβx, hβpos, hβsmooth⟩ := om_chartInverse g x
  set τ : ℝ → ℝ := fun s =>
    intervalIntegral (fun u => Real.sqrt (omCurveSpeedSq g ⇑β0 u)) 0 s
      MeasureTheory.volume with hτ
  obtain ⟨hτsmooth, hτder⟩ := om_arclength_contDiffOn β0.source
    (fun s => omCurveSpeedSq g ⇑β0 s) β0.open_source hβconn hβ0 hβsmooth
    (fun s hs => hβpos s hs)
  have hτderiv : ∀ s ∈ β0.source, 0 < deriv τ s := by
    intro s hs
    have h1 : deriv τ s = Real.sqrt (omCurveSpeedSq g ⇑β0 s) :=
      (hτder s hs).deriv
    rw [h1]
    exact Real.sqrt_pos.mpr (hβpos s hs)
  obtain ⟨Φ, hΦsrc, hΦfun, hΦtgt, hΦconn, hΦsymm⟩ :=
    odm_exists_partialDiffeomorph_of_deriv_pos β0.source τ β0.open_source hβconn
      hτsmooth hτderiv
  have hτ0 : τ 0 = 0 := intervalIntegral.integral_same
  have hΦ0 : Φ 0 = 0 := by
    rwa [hΦfun]
  have h0tgt : (0 : ℝ) ∈ Φ.target := by
    rw [hΦtgt]
    exact ⟨0, hβ0, hτ0⟩
  set α : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞ := Φ.symm.trans β0 with hα
  have hsymmsrc : Φ.symm.source = Φ.target := rfl
  have htrans : α.source = Φ.symm.source ∩ ⇑Φ.symm ⁻¹' β0.source := rfl
  have hsub : Φ.target ⊆ ⇑Φ.symm ⁻¹' β0.source := by
    intro u hu
    have h1 : Φ.symm u ∈ Φ.source := Φ.symm.toPartialEquiv.map_source hu
    rwa [hΦsrc] at h1
  have hαsrc : α.source = Φ.target := by
    rw [htrans, hsymmsrc]
    exact Set.inter_eq_self_of_subset_left hsub
  have hsymm0 : Φ.symm (Φ 0) = 0 :=
    Φ.toPartialEquiv.left_inv (hΦsrc.symm ▸ hβ0)
  rw [hΦ0] at hsymm0
  refine ⟨α, hαsrc.symm ▸ hΦconn, hαsrc.symm ▸ h0tgt, ?_, ?_⟩
  · change β0 (Φ.symm 0) = x
    rwa [hsymm0]
  · intro u hu
    have hutgt : u ∈ Φ.target := hαsrc ▸ hu
    have husym : u ∈ Φ.symm.source := hsymmsrc ▸ hutgt
    have humem : u ∈ Φ.symm.source ∩ ⇑Φ.symm ⁻¹' β0.source := htrans ▸ hu
    have hmem2 : Φ.symm u ∈ β0.source := humem.2
    have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    have hdiff : DifferentiableAt ℝ ⇑Φ.symm u :=
      (Φ.symm.mdifferentiableAt hn husym).differentiableAt
    have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) ⇑β0 (Φ.symm u) :=
      β0.mdifferentiableAt hn hmem2
    have hev : ∀ s, α s = (⇑β0 ∘ ⇑Φ.symm) s := fun s => rfl
    have hspeed := om_curveSpeedSq_eq_of_eventuallyEq_comp g ⇑β0 ⇑Φ.symm u
      hdiff hmdiff (Filter.Eventually.of_forall hev)
    have hderivk : deriv ⇑Φ.symm u = (deriv τ (Φ.symm u))⁻¹ :=
      (hΦsymm u hutgt).deriv
    have hτk : deriv τ (Φ.symm u) =
      Real.sqrt (omCurveSpeedSq g ⇑β0 (Φ.symm u)) :=
      (hτder (Φ.symm u) hmem2).deriv
    have hspos : 0 < omCurveSpeedSq g ⇑β0 (Φ.symm u) := hβpos _ hmem2
    have hne : Real.sqrt (omCurveSpeedSq g ⇑β0 (Φ.symm u)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hspos)
    have hσsq : omCurveSpeedSq g ⇑β0 (Φ.symm u) =
      (Real.sqrt (omCurveSpeedSq g ⇑β0 (Φ.symm u))) ^ 2 :=
      (Real.sq_sqrt (le_of_lt hspos)).symm
    rw [hspeed, hσsq, hderivk, hτk, ← mul_pow, inv_mul_cancel₀ hne, one_pow]

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
/--
[om_exists_affine_of_unitSpeed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma om_exists_affine_of_unitSpeed
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (α : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞)
  (hα : ∀ s ∈ α.source, omCurveSpeedSq g α s = 1)
  (U : Set ℝ) (γ : ℝ → M) (hU : IsOpen U)
  (hγ : omIsUnitSpeedOn g γ U) (t : ℝ) (ht : t ∈ U)
  (hγt : γ t ∈ α.target) :
  ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ c : ℝ, ε * t + c = α.symm (γ t) ∧
    ∀ᶠ s in nhds t, ε * s + c ∈ α.source ∧ γ s = α (ε * s + c) := by
  have hγcont : ContinuousOn γ U := hγ.1.continuousOn
  set W : Set ℝ := U ∩ γ ⁻¹' α.target with hW
  have hWopen : IsOpen W :=
    hγcont.isOpen_inter_preimage hU α.open_target
  have htW : t ∈ W := ⟨ht, hγt⟩
  set k : ℝ → ℝ := ⇑α.symm ∘ γ with hk
  have hkmaps : Set.MapsTo γ W α.symm.source := fun s hs => hs.2
  have hkD : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ k W :=
    α.symm.contMDiffOn_toFun.comp (hγ.1.mono Set.inter_subset_left) hkmaps
  have hkCd : ContDiffOn ℝ ∞ k W := contMDiffOn_iff_contDiffOn.mp hkD
  have hγeq : ∀ s ∈ W, γ s = α (k s) := fun s hs =>
    (α.toPartialEquiv.right_inv hs.2).symm
  have hmdk : ∀ s ∈ W, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k s := by
    intro s hs
    have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    exact (hkD.mdifferentiableOn hn).mdifferentiableAt (hWopen.mem_nhds hs)
  have hsqW : ∀ s ∈ W, (deriv k s) ^ 2 = 1 := by
    intro s hs
    have hks : DifferentiableAt ℝ k s := (hmdk s hs).differentiableAt
    have hkmem : k s ∈ α.source := α.symm.toPartialEquiv.map_source hs.2
    have hβs : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) ⇑α (k s) :=
      α.mdifferentiableAt (by simp) hkmem
    have hWmem : ∀ᶠ s' in nhds s, s' ∈ W := hWopen.mem_nhds hs
    have hevW : ∀ᶠ s' in nhds s, γ s' = (⇑α ∘ k) s' :=
      hWmem.mono fun s' hs' => hγeq s' hs'
    have heq := om_curveSpeedSq_eq_of_eventuallyEq_comp g ⇑α k s hks hβs hevW
    rw [hγ.2 s hs.1, hα (k s) hkmem] at heq
    simpa using heq.symm
  have hderivCd : ContDiffOn ℝ ∞ (deriv k) W :=
    hkCd.deriv_of_isOpen hWopen (by simp)
  have hderivCont : ContinuousAt (deriv k) t :=
    hderivCd.continuousOn.continuousAt (hWopen.mem_nhds htW)
  have hevEq : ∀ᶠ s in nhds t, deriv k s = deriv k t := by
    have h1' := (hderivCont.tendsto).eventually (Metric.ball_mem_nhds _ one_pos)
    have h1 : ∀ᶠ s in nhds t, dist (deriv k s) (deriv k t) < 1 := by
      simpa only [Metric.mem_ball] using h1'
    have h2 : ∀ᶠ s in nhds t, s ∈ W := hWopen.mem_nhds htW
    filter_upwards [h1, h2] with s hs1 hs2
    obtain hs1c | hs1c <;> := sq_eq_one_iff.mp (hsqW s hs2)
      obtain htc | htc := sq_eq_one_iff.mp (hsqW t htW)
    · rw [hs1c, htc]
    · rw [hs1c, htc] at hs1
      norm_num [dist_eq_norm] at hs1
    · rw [hs1c, htc] at hs1
      norm_num [dist_eq_norm] at hs1
    · rw [hs1c, htc]
  have hmemE : {s | deriv k s = deriv k t} ∈ nhds t := hevEq
  obtain ⟨δ, hδpos, hballsub⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem (hWopen.mem_nhds htW) hmemE)
  set J : Set ℝ := Set.Ioo (t - δ) (t + δ) with hJ
  have hJopen : IsOpen J := isOpen_Ioo
  have hJpre : IsPreconnected J := isPreconnected_Ioo
  have htJ : t ∈ J := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have hJsub : J ⊆ W ∩ {s | deriv k s = deriv k t} := by
    intro s hs
    have hs' : s ∈ Set.Ioo (t - δ) (t + δ) := hs
    have hmem : s ∈ Metric.ball t δ := by
      rwa [← Real.ball_eq_Ioo] at hs'
    exact hballsub hmem
  have hdiffJ : DifferentiableOn ℝ (fun s => k s - deriv k t * s) J :=
    ((hkCd.mono (hJsub.trans Set.inter_subset_left)).differentiableOn
      (by simp)).sub
      (differentiableOn_id.const_mul (deriv k t))
  have hderiv0 : J.EqOn (deriv (fun s => k s - deriv k t * s)) 0 := by
    intro s hs
    have hks : DifferentiableAt ℝ k s := (hmdk s (hJsub hs).1).differentiableAt
    have h1 : HasDerivAt (fun s => k s - deriv k t * s)
      (deriv k s - deriv k t * 1) s :=
      hks.hasDerivAt.sub ((hasDerivAt_id s).const_mul (deriv k t))
    have hder : deriv (fun s => k s - deriv k t * s) s =
      deriv k s - deriv k t * 1 := h1.deriv
    have hsJ : deriv k s = deriv k t := (hJsub hs).2
    rw [hder, hsJ, mul_one, sub_self]
    rfl
  obtain ⟨c, hc⟩ := hJopen.exists_is_const_of_deriv_eq_zero hJpre hdiffJ hderiv0
  have hkc : ∀ x ∈ J, k x = deriv k t * x + c := by
    intro x hx
    have hxc : k x - deriv k t * x = c := hc x hx
    linarith
  have hkt : k t = deriv k t * t + c := hkc t htJ
  refine ⟨deriv k t, sq_eq_one_iff.mp (hsqW t htW), c, hkt.symm, ?_⟩
  have hJnhds : J ∈ nhds t := hJopen.mem_nhds htJ
  filter_upwards [hJnhds] with s hs
  have hsmem : k s ∈ α.source := α.symm.toPartialEquiv.map_source ((hJsub hs).1).2
  constructor
  · rw [(hkc s hs).symm]
    exact hsmem
  · rw [(hkc s hs).symm]
    exact hγeq s (hJsub hs).1

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
/--
[om_unitSpeed_localData](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
chart composed with an affine map, on an open set where it is injective. -/
private lemma om_unitSpeed_localData
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (U : Set ℝ) (γ : ℝ → M) (hU : IsOpen U)
  (hγ : omIsUnitSpeedOn g γ U) (t : ℝ) (ht : t ∈ U) :
  ∃ α : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞,
  ∃ ε c : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ D : Set ℝ, IsOpen D ∧ t ∈ D ∧
    (∀ s ∈ D, ε * s + c ∈ α.source ∧ γ s = α (ε * s + c)) ∧
    Set.InjOn γ D := by
  obtain ⟨α, -, hα0mem, hα0, hαspeed⟩ := om_exists_unitSpeedChart g (γ t)
  have hγt : γ t ∈ α.target := hα0 ▸ α.toPartialEquiv.map_source hα0mem
  obtain ⟨ε, hε, c, -, hev⟩ :=
    om_exists_affine_of_unitSpeed g α hαspeed U γ hU hγ t ht hγt
  obtain ⟨D, hDsub, hDopen, htD⟩ := mem_nhds_iff.mp hev
  refine ⟨α, ε, c, hε, D, hDopen, htD, fun s hs => hDsub hs, ?_⟩
  intro s₁ hs₁ s₂ hs₂ h12
  have h1 := (hDsub hs₁).1
  have h2 := (hDsub hs₂).1
  have h3 := (hDsub hs₁).2
  have h4 := (hDsub hs₂).2
  have hne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hsc : ε * s₁ + c = ε * s₂ + c :=
    α.toPartialEquiv.injOn h1 h2 (h3.symm.trans (h12.trans h4))
  have hmul : ε * s₁ = ε * s₂ := by linarith
  exact mul_left_cancel₀ hne hmul

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
/--
[om_affine_partialDiffeo](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
diffeomorphism of `ℝ`. -/
private lemma om_affine_partialDiffeo (ε c : ℝ) (hε : ε = 1 ∨ ε = -1) :
  ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
    (⇑Φ : ℝ → ℝ) = (fun s => ε * s + c) ∧ Φ.source = Set.univ := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have haffD : ContDiff ℝ ∞ (fun s : ℝ => ε * s + c) :=
    (contDiff_const.mul contDiff_id).add contDiff_const
  have hinvD : ContDiff ℝ ∞ (fun y : ℝ => ε * (y - c)) :=
    contDiff_const.mul (contDiff_id.sub contDiff_const)
  obtain ⟨Φ, hsrc, -, hfun, -⟩ := odm_exists_partialDiffeomorph_of_invOn
    (fun s : ℝ => ε * s + c) (fun y : ℝ => ε * (y - c))
    Set.univ Set.univ isOpen_univ isOpen_univ
    (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
    ⟨fun s _ => by
      change ε * (ε * s + c - c) = s
      have h : ε * (ε * s + c - c) = (ε * ε) * s := by ring
      rw [h, hε2, one_mul],
    fun y _ => by
      change ε * (ε * (y - c)) + c = y
      have h : ε * (ε * (y - c)) + c = (ε * ε) * (y - c) + c := by ring
      rw [h, hε2, one_mul, sub_add_cancel]⟩
    (haffD.contMDiff.contMDiffOn) (hinvD.contMDiff.contMDiffOn)
  exact ⟨Φ, hfun, hsrc⟩

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
/--
[om_isLocalDiffeomorphAt_of_unitSpeed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma om_isLocalDiffeomorphAt_of_unitSpeed
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (U : Set ℝ) (γ : ℝ → M) (hU : IsOpen U)
  (hγ : omIsUnitSpeedOn g γ U) (t : ℝ) (ht : t ∈ U) :
  IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ t := by
  obtain ⟨α, ε, c, hε, D, hDopen, htD, hDprop, -⟩ :=
    om_unitSpeed_localData g U γ hU hγ t ht
  obtain ⟨Φaff, hΦaff, hΦaffsrc⟩ := om_affine_partialDiffeo ε c hε
  have hmem : Φaff t ∈ α.source := hΦaff.symm ▸ (hDprop t htD).1
  have hFmem : t ∈ (Φaff.trans α).source := by
    have h : (Φaff.trans α).source = Φaff.source ∩ ⇑Φaff ⁻¹' α.source := rfl
    rw [h]
    exact ⟨hΦaffsrc.symm ▸ Set.mem_univ t, hmem⟩
  have hF : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ ⇑(Φaff.trans α) t :=
    PartialDiffeomorph.isLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ _ hFmem
  have hevF : γ =ᶠ[nhds t] ⇑(Φaff.trans α) := by
    have hDmem : ∀ᶠ s in nhds t, s ∈ D := hDopen.mem_nhds htD
    refine hDmem.mono fun s hs => ?_
    have h2 := (hDprop s hs).2
    change γ s = (Φaff.trans α) s
    change γ s = α (Φaff s)
    rw [hΦaff]
    change γ s = α (ε * s + c)
    exact h2
  exact odm_isLocalDiffeomorphAt_congr_of_eventuallyEq hF hevF

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
/--
[om_exists_injOn_of_unitSpeed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma om_exists_injOn_of_unitSpeed
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (U : Set ℝ) (γ : ℝ → M) (hU : IsOpen U)
  (hγ : omIsUnitSpeedOn g γ U) (t : ℝ) (ht : t ∈ U) :
  ∃ δ : ℝ, 0 < δ ∧ Set.InjOn γ (Set.Ioo (t - δ) (t + δ)) := by
  obtain ⟨α, ε, c, hε, D, hDopen, htD, hDprop, hInj⟩ :=
    om_unitSpeed_localData g U γ hU hγ t ht
  obtain ⟨δ, hδpos, hballsub⟩ := Metric.mem_nhds_iff.mp (hDopen.mem_nhds htD)
  refine ⟨δ, hδpos, ?_⟩
  apply hInj.mono
  intro s hs
  have hs' : s ∈ Set.Ioo (t - δ) (t + δ) := hs
  have hmem : s ∈ Metric.ball t δ := by
    rwa [← Real.ball_eq_Ioo] at hs'
  exact hballsub hmem

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
/--
[om_image_mem_nhds_of_unitSpeed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma om_image_mem_nhds_of_unitSpeed
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (U : Set ℝ) (γ : ℝ → M) (hU : IsOpen U)
  (hγ : omIsUnitSpeedOn g γ U) (t : ℝ) (ht : t ∈ U)
  (W : Set ℝ) (hW : W ∈ nhds t) :
  γ '' W ∈ nhds (γ t) := by
  obtain ⟨α, ε, c, hε, D, hDopen, htD, hDprop, -⟩ :=
    om_unitSpeed_localData g U γ hU hγ t ht
  obtain ⟨Φaff, hΦaff, hΦaffsrc⟩ := om_affine_partialDiffeo ε c hε
  have htW : t ∈ W := mem_of_mem_nhds hW
  have htI : t ∈ interior W := mem_interior_iff_mem_nhds.mpr hW
  set E : Set ℝ := D ∩ interior W with hE
  have hEopen : IsOpen E := hDopen.inter isOpen_interior
  have htE : t ∈ E := ⟨htD, htI⟩
  have hsub1 : (fun s => ε * s + c) '' E ⊆ α.source := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact (hDprop s hs.1).1
  have haffE : IsOpen ((fun s => ε * s + c) '' E) := by
    have himg : (fun s => ε * s + c) '' E = Φaff '' E := by rw [hΦaff]
    rwa [himg]
      hEopen (fun y _ => by
        change y ∈ Φaff.source
        rw [hΦaffsrc]
        exact Set.mem_univ y)
  have hαimg : IsOpen (⇑α '' ((fun s => ε * s + c) '' E)) :=
    α.toOpenPartialHomeomorph.isOpen_image_of_subset_source haffE hsub1
  have himgEq : γ '' E = ⇑α '' ((fun s => ε * s + c) '' E) := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨ε * s + c, ⟨s, hs, rfl⟩, (hDprop s hs.1).2.symm⟩
    · rintro ⟨-, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨s, ⟨hs.1, hs.2⟩, (by simpa using (hDprop s hs.1).2)⟩
  have hmem : γ '' E ∈ nhds (γ t) := himgEq.symm ▸
    hαimg.mem_nhds ⟨ε * t + c, ⟨t, htE, rfl⟩, (hDprop t htD).2.symm⟩
  have hEW : E ⊆ W :=
    (Set.inter_subset_right (s := D) (t := interior W)).trans interior_subset
  exact Filter.mem_of_superset hmem
    (fun y hy => by obtain ⟨s, hs, rfl⟩ := hy; exact ⟨s, hEW hs, rfl⟩)
section IdentityTheorem
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M] [T2Space M]

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M] [T2Space M]
/--
[om_eqOn_of_unitSpeed_of_eventuallyEq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
near one point agree everywhere. -/
private theorem om_eqOn_of_unitSpeed_of_eventuallyEq
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (I : Set ℝ) (hIopen : IsOpen I) (hIpre : IsPreconnected I)
  (γ1 γ2 : ℝ → M) (h1 : omIsUnitSpeedOn g γ1 I) (h2 : omIsUnitSpeedOn g γ2 I)
  (t0 : ℝ) (ht0 : t0 ∈ I) (h0 : γ1 =ᶠ[nhds t0] γ2) :
  Set.EqOn γ1 γ2 I := by
  set u : Set ℝ := {t | γ1 =ᶠ[nhds t] γ2} with hu
  have huopen : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact eventually_eventuallyEq_nhds.mpr ht
  have hIu : (I ∩ u).Nonempty := ⟨t0, ht0, h0⟩
  have hsub : I ⊆ u := by
    apply hIpre.subset_of_closure_inter_subset huopen hIu
    intro t ht
    obtain ⟨htcl, htI⟩ := ht
    have hImem : I ∈ nhds t := hIopen.mem_nhds htI
    have hcont1 : ContinuousAt γ1 t := h1.1.continuousOn.continuousAt hImem
    have hcont2 : ContinuousAt γ2 t := h2.1.continuousOn.continuousAt hImem
    have hfreq : ∃ᶠ s in nhds t, γ1 s = γ2 s :=
      (mem_closure_iff_frequently.mp htcl).mono fun s hs => hs.self_of_nhds
    have hteq : γ1 t = γ2 t :=
      tendsto_nhds_unique_of_frequently_eq hcont1 hcont2 hfreq
    obtain ⟨α, -, hα0mem, hα0, hαspeed⟩ := om_exists_unitSpeedChart g (γ1 t)
    have hγt1 : γ1 t ∈ α.target := hα0 ▸ α.toPartialEquiv.map_source hα0mem
    have hγt2 : γ2 t ∈ α.target := hteq ▸ hγt1
    obtain ⟨ε1, -, c1, -, hev1⟩ :=
      om_exists_affine_of_unitSpeed g α hαspeed I γ1 hIopen h1 t htI hγt1
    obtain ⟨ε2, -, c2, -, hev2⟩ :=
      om_exists_affine_of_unitSpeed g α hαspeed I γ2 hIopen h2 t htI hγt2
    have hev : ∀ᶠ s in nhds t,
      (ε1 * s + c1 ∈ α.source ∧ γ1 s = α (ε1 * s + c1)) ∧
      (ε2 * s + c2 ∈ α.source ∧ γ2 s = α (ε2 * s + c2)) :=
      hev1.and hev2
    obtain ⟨δ, hδpos, hball⟩ := Metric.mem_nhds_iff.mp hev
    have hmem7 : Metric.ball t (δ / 2) ∈ nhds t :=
      Metric.ball_mem_nhds t (by linarith)
    have hfreqU : ∃ᶠ s in nhds t, s ∈ u := mem_closure_iff_frequently.mp htcl
    obtain ⟨s, hsu, hsball⟩ := (hfreqU.and_eventually hmem7).exists
    obtain ⟨F, hFsub, hFopen, hsF⟩ := mem_nhds_iff.mp hsu
    set E : Set ℝ := Metric.ball s (δ / 2) ∩ F with hE
    have hEopen : IsOpen E := Metric.isOpen_ball.inter hFopen
    have hsE : s ∈ E := ⟨Metric.mem_ball_self (by linarith), hsF⟩
    have hEball : E ⊆ Metric.ball t δ := by
      intro y hy
      have h1d : dist y s < δ / 2 := Metric.mem_ball.mp hy.1
      have h2d : dist s t < δ / 2 := hsball
      refine Metric.mem_ball.mpr ?_
      calc dist y t ≤ dist y s + dist s t := dist_triangle y s t
        _ < δ := by linarith
    have hEprop : ∀ y ∈ E, ε1 * y + c1 ∈ α.source ∧ ε2 * y + c2 ∈ α.source ∧
      α (ε1 * y + c1) = α (ε2 * y + c2) := by
      intro y hy
      have hyt := hball (hEball hy)
      have hFy : γ1 y = γ2 y := hFsub hy.2
      refine ⟨(hyt.1).1, (hyt.2).1, ?_⟩
      calc α (ε1 * y + c1) = γ1 y := ((hyt.1).2).symm
        _ = γ2 y := hFy
        _ = α (ε2 * y + c2) := (hyt.2).2
    have haff : ∀ y ∈ E, ε1 * y + c1 = ε2 * y + c2 := by
      intro y hy
      obtain ⟨hm1, hm2, heq⟩ := hEprop y hy
      exact α.toPartialEquiv.injOn hm1 hm2 heq
    obtain ⟨r, hrpos, hrball⟩ := Metric.mem_nhds_iff.mp (hEopen.mem_nhds hsE)
    have hs2E : s + r / 2 ∈ E := by
      apply hrball
      rw [Metric.mem_ball, dist_eq_norm]
      have hrw : (s + r / 2) - s = r / 2 := by ring
      rw [hrw, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have hne12 : s ≠ s + r / 2 := by
      intro h
      have h0' : (r / 2 : ℝ) = 0 := by linarith
      linarith
    have e1 := haff s hsE
    have e2 := haff (s + r / 2) hs2E
    have hkey : (ε1 - ε2) * (s - (s + r / 2)) = 0 := by
      have h1' : ε1 * s - ε2 * s = c2 - c1 := by linarith
      have h2' : ε1 * (s + r / 2) - ε2 * (s + r / 2) = c2 - c1 := by linarith
      have hrr : (ε1 - ε2) * (s - (s + r / 2)) =
        (ε1 * s - ε2 * s) - (ε1 * (s + r / 2) - ε2 * (s + r / 2)) := by ring
      rw [hrr, h1', h2', sub_self]
    have hε : ε1 = ε2 := by
      obtain h | h := mul_eq_zero.mp hkey
      · linarith
      · exact absurd (sub_eq_zero.mp h) hne12
    have hc : c1 = c2 := by
      have hcc := haff s hsE
      rw [hε] at hcc
      linarith
    change γ1 =ᶠ[nhds t] γ2
    filter_upwards [Metric.ball_mem_nhds t hδpos] with y hy
    have hyt := hball hy
    calc γ1 y = α (ε1 * y + c1) := (hyt.1).2
      _ = α (ε2 * y + c2) := by rw [hε, hc]
      _ = γ2 y := ((hyt.2).2).symm
  intro t ht
  exact (hsub ht).self_of_nhds
section MaximalCurve
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M] [T2Space M]

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M] [T2Space M]
/--
[om_exists_maximal_unitSpeed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
curves, which absorbs every admissible curve. -/
private lemma om_exists_maximal_unitSpeed
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (α0 : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞)
  (hα0src : α0.source.OrdConnected) (hα00 : (0 : ℝ) ∈ α0.source)
  (hα0speed : ∀ s ∈ α0.source, omCurveSpeedSq g α0 s = 1) :
  ∃ D γ, omAdmissible g α0 D γ ∧
    ∀ J δ, omAdmissible g α0 J δ → J ⊆ D ∧ Set.EqOn δ γ J := by
  set S : Set (Set ℝ) := {J | ∃ δ, omAdmissible g α0 J δ}
  set D : Set ℝ := ⋃₀ S
  have hex : ∀ t : ℝ, ∃ J δ, (t ∈ D → omAdmissible g α0 J δ ∧ t ∈ J) := by
    intro t
    by_cases ht : t ∈ D
    · obtain ⟨J, hJ, htJ⟩ := ht
      obtain ⟨δ, hδ⟩ := hJ
      exact ⟨J, δ, fun _ => ⟨hδ, htJ⟩⟩
    · exact ⟨∅, fun _ => α0 0, fun h => absurd h ht⟩
  choose J0 δ0 hJ0 using hex
  set γ : ℝ → M := fun t => δ0 t t
  have hDsub : ∀ J δ, omAdmissible g α0 J δ → J ⊆ D := by
    intro J δ hJδ t htJ
    exact Set.mem_sUnion.mpr ⟨J, ⟨δ, hJδ⟩, htJ⟩
  have hcons : ∀ J δ J' δ', omAdmissible g α0 J δ → omAdmissible g α0 J' δ' →
    Set.EqOn δ δ' (J ∩ J') := by
    intro J δ J' δ' h h'
    have hJJopen : IsOpen (J ∩ J') := h.1.inter h'.1
    have hJJconn := h.2.1.inter h'.2.1
    have hJJpre : IsPreconnected (J ∩ J') := hJJconn.isPreconnected
    have h0JJ : (0 : ℝ) ∈ J ∩ J' := ⟨h.2.2.1, h'.2.2.1⟩
    have hev : δ =ᶠ[nhds 0] δ' := h.2.2.2.2.trans h'.2.2.2.2.symm
    have hu : omIsUnitSpeedOn g δ (J ∩ J') :=
      ⟨h.2.2.2.1.1.mono Set.inter_subset_left, fun t ht => h.2.2.2.1.2 t ht.1⟩
    have hu' : omIsUnitSpeedOn g δ' (J ∩ J') :=
      ⟨h'.2.2.2.1.1.mono Set.inter_subset_right, fun t ht => h'.2.2.2.1.2 t ht.2⟩
    exact om_eqOn_of_unitSpeed_of_eventuallyEq g (J ∩ J') hJJopen hJJpre δ δ'
      hu hu' 0 h0JJ hev
  have hγeq : ∀ J δ, omAdmissible g α0 J δ → Set.EqOn δ γ J := by
    intro J δ hJδ t htJ
    have htD : t ∈ D := hDsub J δ hJδ htJ
    have hmem : t ∈ J ∩ J0 t := ⟨htJ, (hJ0 t htD).2⟩
    have h1 : δ t = δ0 t t := hcons J δ (J0 t) (δ0 t) hJδ (hJ0 t htD).1 hmem
    change δ t = δ0 t t
    exact h1
  have hα0adm : omAdmissible g α0 α0.source ⇑α0 :=
    ⟨α0.open_source, hα0src, hα00, ⟨α0.contMDiffOn_toFun, hα0speed⟩,
      Filter.EventuallyEq.refl _ _⟩
  have h0D : (0 : ℝ) ∈ D := hDsub _ _ hα0adm hα00
  have hDopen : IsOpen D := by
    apply isOpen_sUnion
    intro J hJ
    obtain ⟨δ, hδ⟩ := hJ
    exact hδ.1
  have hDpre : IsPreconnected D := by
    apply isPreconnected_sUnion 0 S _ _
    · intro s hs
      obtain ⟨δ, hδ⟩ := hs
      exact hδ.2.2.1
    · intro s hs
      obtain ⟨δ, hδ⟩ := hs
      exact hδ.2.1.isPreconnected
  have hDconn : D.OrdConnected := isPreconnected_iff_ordConnected.mp hDpre
  have hγsmooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ D := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro t htD
    have hadm := (hJ0 t htD).1
    have htJt := (hJ0 t htD).2
    refine ⟨J0 t, hadm.1, htJt, ?_⟩
    exact (ContMDiffOn.congr hadm.2.2.2.1.1
      (fun s hs => (hγeq _ _ hadm hs).symm)).mono Set.inter_subset_right
  have hγspeed : ∀ t ∈ D, omCurveSpeedSq g γ t = 1 := by
    intro t htD
    have hadm := (hJ0 t htD).1
    have htJt := (hJ0 t htD).2
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) (δ0 t) t :=
      (hadm.2.2.2.1.1.mdifferentiableOn (by simp)).mdifferentiableAt
        (hadm.1.mem_nhds htJt)
    have hev : γ =ᶠ[nhds t] (δ0 t) ∘ id :=
      Filter.eventuallyEq_of_mem (hadm.1.mem_nhds htJt)
        (fun s hs => (hγeq _ _ hadm hs).symm)
    have hcomp := om_curveSpeedSq_eq_of_eventuallyEq_comp g (δ0 t) id t
      differentiableAt_id hmd hev
    have h1 : omCurveSpeedSq g (δ0 t) (id t) = 1 := hadm.2.2.2.1.2 t htJt
    rw [hcomp, h1, (hasDerivAt_id t).deriv, one_pow, mul_one]
  have hγev : γ =ᶠ[nhds 0] ⇑α0 :=
    Filter.eventuallyEq_of_mem (α0.open_source.mem_nhds hα00)
      (fun s hs => (hγeq _ _ hα0adm hs).symm)
  have hγadm : omAdmissible g α0 D γ :=
    ⟨hDopen, hDconn, h0D, ⟨hγsmooth, hγspeed⟩, hγev⟩
  exact ⟨D, γ, hγadm, fun J δ h => ⟨hDsub J δ h, hγeq J δ h⟩⟩
section AbsorbMaximal
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M] [T2Space M]

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M] [T2Space M]
/--
[om_maximal_unitSpeed_absorb](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
agrees with the maximal curve near one common point is absorbed by it. -/
private lemma om_maximal_unitSpeed_absorb
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (α0 : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞)
  (D : Set ℝ) (γ : ℝ → M)
  (hDadm : omAdmissible g α0 D γ)
  (hmax : ∀ J δ, omAdmissible g α0 J δ → J ⊆ D ∧ Set.EqOn δ γ J)
  (J : Set ℝ) (δ : ℝ → M)
  (hJopen : IsOpen J) (hJconn : J.OrdConnected)
  (hδ : omIsUnitSpeedOn g δ J)
  (t : ℝ) (ht : t ∈ D ∩ J) (hev : δ =ᶠ[nhds t] γ) :
  J ⊆ D ∧ Set.EqOn δ γ J := by
  classical
  obtain ⟨hDopen, hDconn, h0D, hγunit, hγev⟩ := hDadm
  have hDJopen : IsOpen (D ∩ J) := hDopen.inter hJopen
  have hDJconn := hDconn.inter hJconn
  have hDJpre : IsPreconnected (D ∩ J) := hDJconn.isPreconnected
  have hδDJ : omIsUnitSpeedOn g δ (D ∩ J) :=
    ⟨hδ.1.mono Set.inter_subset_right, fun s hs => hδ.2 s hs.2⟩
  have hγDJ : omIsUnitSpeedOn g γ (D ∩ J) :=
    ⟨hγunit.1.mono Set.inter_subset_left, fun s hs => hγunit.2 s hs.1⟩
  have hEqDJ : Set.EqOn δ γ (D ∩ J) :=
    om_eqOn_of_unitSpeed_of_eventuallyEq g (D ∩ J) hDJopen hDJpre δ γ
      hδDJ hγDJ t ht hev
  set J' : Set ℝ := D ∪ J
  set γ' : ℝ → M := fun s => if s ∈ D then γ s else δ s
  have hJ'open : IsOpen J' := hDopen.union hJopen
  have hJ'conn : J'.OrdConnected :=
    isPreconnected_iff_ordConnected.mp
      (IsPreconnected.union t ht.1 ht.2 hDconn.isPreconnected
        hJconn.isPreconnected)
  have h0J' : (0 : ℝ) ∈ J' := Or.inl h0D
  have hγ'eq : ∀ s, γ' s = (if s ∈ D then γ s else δ s) := fun s => rfl
  have hγ'D : Set.EqOn γ γ' D := fun s hs => by
    rw [hγ'eq s, ite_eq_left hs]
  have hγ'J : Set.EqOn δ γ' J := fun s hs => by
    by_cases hsD : s ∈ D
    · rw [hγ'eq s, ite_eq_left hsD]
      exact hEqDJ ⟨hsD, hs⟩
    · rw [hγ'eq s, ite_eq_right hsD]
  have hspeed_of : ∀ (U : Set ℝ) (β : ℝ → M), IsOpen U → omIsUnitSpeedOn g β U →
    Set.EqOn β γ' U → ∀ s ∈ U, omCurveSpeedSq g γ' s = 1 := by
    intro U β hUopen hβ hEq s hs
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) β s :=
      (hβ.1.mdifferentiableOn (by simp)).mdifferentiableAt (hUopen.mem_nhds hs)
    have hevS : γ' =ᶠ[nhds s] β ∘ id :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hs) (fun q hq => (hEq hq).symm)
    have hcomp := om_curveSpeedSq_eq_of_eventuallyEq_comp g β id s
      differentiableAt_id hmd hevS
    have h1 : omCurveSpeedSq g β (id s) = 1 := hβ.2 s hs
    rw [hcomp, h1, (hasDerivAt_id s).deriv, one_pow, mul_one]
  have hγ'smooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ' J' := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro s hs
    by_cases hsD : s ∈ D
    · refine ⟨D, hDopen, hsD, ?_⟩
      exact (ContMDiffOn.congr hγunit.1
        (fun q hq => (hγ'D hq).symm)).mono Set.inter_subset_right
    · have hsU : s ∈ D ∪ J := hs
      have hsJ : s ∈ J := (Set.mem_or_mem_of_mem_union hsU).resolve_left hsD
      refine ⟨J, hJopen, hsJ, ?_⟩
      exact (ContMDiffOn.congr hδ.1
        (fun q hq => (hγ'J hq).symm)).mono Set.inter_subset_right
  have hγ'speed : ∀ s ∈ J', omCurveSpeedSq g γ' s = 1 := by
    intro s hs
    by_cases hsD : s ∈ D
    · exact hspeed_of D γ hDopen hγunit hγ'D s hsD
    · have hsU : s ∈ D ∪ J := hs
      have hsJ : s ∈ J := (Set.mem_or_mem_of_mem_union hsU).resolve_left hsD
      exact hspeed_of J δ hJopen hδ hγ'J s hsJ
  have hγ'ev : γ' =ᶠ[nhds 0] ⇑α0 := by
    have h1 : γ' =ᶠ[nhds 0] γ :=
      Filter.eventuallyEq_of_mem (hDopen.mem_nhds h0D)
        (fun s hs => (hγ'D hs).symm)
    exact h1.trans hγev
  have hJ'adm : omAdmissible g α0 J' γ' :=
    ⟨hJ'open, hJ'conn, h0J', ⟨hγ'smooth, hγ'speed⟩, hγ'ev⟩
  have hsub := (hmax J' γ' hJ'adm).1
  have hJsub : J ⊆ D := Set.subset_union_right.trans hsub
  refine ⟨hJsub, fun s hs => ?_⟩
  exact hEqDJ ⟨hJsub hs, hs⟩
section OntoMaximal
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M] [T2Space M] [ConnectedSpace M]

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M] [T2Space M] [ConnectedSpace M]
/--
[om_maximal_unitSpeed_image_eq_univ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma om_maximal_unitSpeed_image_eq_univ
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (α0 : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞)
  (D : Set ℝ) (γ : ℝ → M)
  (hDadm : omAdmissible g α0 D γ)
  (hmax : ∀ J δ, omAdmissible g α0 J δ → J ⊆ D ∧ Set.EqOn δ γ J) :
  γ '' D = Set.univ := by
  obtain ⟨hDopen, hDconnA, h0D, hγunit, hγevA⟩ := hDadm
  have hSopen : IsOpen (γ '' D) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨t, htD, rfl⟩
    exact om_image_mem_nhds_of_unitSpeed g D γ hDopen hγunit t htD D
      (hDopen.mem_nhds htD)
  have hSclosed : IsClosed (γ '' D) := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    obtain ⟨α, hαconn, hα0mem, hα0, hαspeed⟩ := om_exists_unitSpeedChart g y
    have hytgt : y ∈ α.target := hα0 ▸ α.toPartialEquiv.map_source hα0mem
    have hfreqS : ∃ᶠ z in nhds y, z ∈ γ '' D := mem_closure_iff_frequently.mp hy
    have hmemT : α.target ∈ nhds y := α.open_target.mem_nhds hytgt
    obtain ⟨z, hzS, hzT⟩ := (hfreqS.and_eventually hmemT).exists
    obtain ⟨t1, ht1D, rfl⟩ := hzS
    obtain ⟨ε, hε, c, -, hev⟩ :=
      om_exists_affine_of_unitSpeed g α hαspeed D γ hDopen hγunit t1 ht1D hzT
    have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    set L : Set ℝ := {s | ε * s + c ∈ α.source}
    have hLopen : IsOpen L :=
      α.open_source.preimage ((continuous_const.mul continuous_id).add continuous_const)
    have hLimg : L = (fun u => ε * (u - c)) '' α.source := by
      ext s
      constructor
      · intro hs
        refine ⟨ε * s + c, hs, ?_⟩
        change ε * ((ε * s + c) - c) = s
        have hrr : ε * ((ε * s + c) - c) = (ε * ε) * s := by ring
        rw [hrr, hε2, one_mul]
      · rintro ⟨u, hu, rfl⟩
        change ε * (ε * (u - c)) + c ∈ α.source
        have hrr : ε * (ε * (u - c)) + c = u := by
          have h : ε * (ε * (u - c)) + c = (ε * ε) * (u - c) + c := by ring
          rw [h, hε2, one_mul, sub_add_cancel]
        rwa [hrr]
    have hLconn : L.OrdConnected :=
      isPreconnected_iff_ordConnected.mp (hLimg ▸
        (hαconn.isPreconnected.image _
          (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn))
    set δ : ℝ → M := ⇑α ∘ (fun s => ε * s + c)
    have haffM : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => ε * s + c) L :=
      (((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff).contMDiffOn
    have hδsmooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ δ L :=
      α.contMDiffOn_toFun.comp haffM (fun s hs => hs)
    have hδspeed : ∀ s ∈ L, omCurveSpeedSq g δ s = 1 := by
      intro s hs
      have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) ⇑α (ε * s + c) :=
        α.mdifferentiableAt (by simp) hs
      have hk : DifferentiableAt ℝ (fun s => ε * s + c) s :=
        ((differentiableAt_const ε).mul differentiableAt_id).add (differentiableAt_const c)
      have hevS : δ =ᶠ[nhds s] ⇑α ∘ (fun s => ε * s + c) :=
        Filter.EventuallyEq.refl _ _
      have hcomp := om_curveSpeedSq_eq_of_eventuallyEq_comp g ⇑α _ s hk hmd hevS
      have h1 : omCurveSpeedSq g ⇑α (ε * s + c) = 1 := hαspeed _ hs
      have hder : deriv (fun s => ε * s + c) s = ε := by
        have h := (((hasDerivAt_id s).const_mul ε).add_const c).deriv
        rwa [mul_one] at h
      rw [hcomp, hder, h1, pow_two, hε2, mul_one]
    have ht1L : t1 ∈ L := (hev.self_of_nhds).1
    have hev1 : δ =ᶠ[nhds t1] γ := hev.mono fun s hs => (hs.2).symm
    have hprobe : omAdmissible g α0 D γ := ⟨hDopen, hDconnA, h0D, hγunit, hγevA⟩
    obtain ⟨hLsub, hEq⟩ := om_maximal_unitSpeed_absorb g α0 D γ hprobe hmax L δ
      hLopen hLconn ⟨hδsmooth, hδspeed⟩ t1 ⟨ht1D, ht1L⟩ hev1
    set sstar : ℝ := -ε * c
    have hsstar : ε * sstar + c = 0 := by
      change ε * (-ε * c) + c = 0
      have h : ε * (-ε * c) + c = (1 - ε * ε) * c := by ring
      rw [h, hε2, sub_self, zero_mul]
    have hsstarL : sstar ∈ L := by
      change ε * sstar + c ∈ α.source
      rwa [hsstar]
    have hmem : γ sstar = y := by
      have e1 : δ sstar = γ sstar := hEq hsstarL
      have e2 : δ sstar = α (ε * sstar + c) := rfl
      rwa [← e1, e2, hsstar]
    exact ⟨sstar, hLsub hsstarL, hmem⟩
  exact IsClopen.eq_univ ⟨hSclosed, hSopen⟩ ⟨γ 0, 0, h0D, rfl⟩
section PeriodicCoincidence
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M] [T2Space M]

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M] [T2Space M]
/--
[om_maximal_unitSpeed_periodic_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
same point twice, the domain is everything and the curve is periodic. -/
private lemma om_maximal_unitSpeed_periodic_of_eq
  (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
    (fun x : M => TangentSpace (𝓡 1) x))
  (α0 : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞)
  (D : Set ℝ) (γ : ℝ → M)
  (hDadm : omAdmissible g α0 D γ)
  (hmax : ∀ J δ, omAdmissible g α0 J δ → J ⊆ D ∧ Set.EqOn δ γ J)
  (t1 t2 : ℝ) (ht1 : t1 ∈ D) (ht2 : t2 ∈ D) (hlt : t1 < t2)
  (heq : γ t1 = γ t2) :
  D = Set.univ ∧ ∀ s : ℝ, γ (s + (t2 - t1)) = γ s := by
  obtain ⟨hDopen, hDconn, h0D, hγunit, hγev⟩ := hDadm
  have hprobe : omAdmissible g α0 D γ := ⟨hDopen, hDconn, h0D, hγunit, hγev⟩
  set T : ℝ := t2 - t1 with hTdef
  have hTpos : 0 < T := by rw [hTdef]; linarith
  obtain ⟨α, hαconn, hα0mem, hα0, hαspeed⟩ := om_exists_unitSpeedChart g (γ t1)
  have hγt1 : γ t1 ∈ α.target := hα0 ▸ α.toPartialEquiv.map_source hα0mem
  have hγt2 : γ t2 ∈ α.target := heq ▸ hγt1
  obtain ⟨ε1, hε1, c1, hcen1, hev1⟩ :=
    om_exists_affine_of_unitSpeed g α hαspeed D γ hDopen hγunit t1 ht1 hγt1
  obtain ⟨ε2, hε2, c2, hcen2, hev2⟩ :=
    om_exists_affine_of_unitSpeed g α hαspeed D γ hDopen hγunit t2 ht2 hγt2
  have hcenter : ε1 * t1 + c1 = ε2 * t2 + c2 := by
    rw [hcen1, hcen2, heq]
  -- Shifted curves `γ ∘ (slope * · + shift)` on the preimage domain are unit-speed.
  have hshift : ∀ (e d : ℝ), e * e = 1 → ∀ (U : Set ℝ) (δk : ℝ → M),
    IsOpen U → U = (fun s => e * s + d) ⁻¹' D →
    δk = γ ∘ (fun s => e * s + d) → omIsUnitSpeedOn g δk U := by
    intro e d he2 U δk hUopen hUeq hδkeq
    have hinner : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => e * s + d) U :=
      (((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff).contMDiffOn
    have hmaps : Set.MapsTo (fun s => e * s + d) U D := by
      intro s hs
      have hs' : s ∈ (fun s => e * s + d) ⁻¹' D := by rwa [← hUeq]
      exact hs'
    have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ (γ ∘ (fun s => e * s + d)) U :=
      hγunit.1.comp hinner hmaps
    constructor
    · rwa [hδkeq]
    · intro s hs
      have hsD : e * s + d ∈ D := by
        have hs' : s ∈ (fun s => e * s + d) ⁻¹' D := by rwa [← hUeq]
        exact hs'
      have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) γ (e * s + d) :=
        (hγunit.1.mdifferentiableOn (by simp)).mdifferentiableAt (hDopen.mem_nhds hsD)
      have hk : DifferentiableAt ℝ (fun s => e * s + d) s :=
        ((differentiableAt_const e).mul differentiableAt_id).add (differentiableAt_const d)
      have hevS : δk =ᶠ[nhds s] γ ∘ (fun s => e * s + d) := by
        rw [hδkeq]
      have hcomp2 := om_curveSpeedSq_eq_of_eventuallyEq_comp g γ _ s hk hmd hevS
      have h1 : omCurveSpeedSq g γ ((fun s => e * s + d) s) = 1 := hγunit.2 _ hsD
      have hder : deriv (fun s => e * s + d) s = e := by
        have h := (((hasDerivAt_id s).const_mul e).add_const d).deriv
        rwa [mul_one] at h
      rw [hcomp2, hder, h1, pow_two, he2, mul_one]
  obtain hεeq | hεne := eq_or_ne ε1 ε2
  · -- Translation case: the orientations agree, so `T` is a period.
    rw [hεeq] at hcenter
    set Jp : Set ℝ := (fun s => 1 * s + T) ⁻¹' D
    set Jm : Set ℝ := (fun s => 1 * s + -T) ⁻¹' D
    set dp : ℝ → M := γ ∘ (fun s => 1 * s + T)
    set dm : ℝ → M := γ ∘ (fun s => 1 * s + -T)
    have hJpopen : IsOpen Jp :=
      hDopen.preimage ((continuous_const.mul continuous_id).add continuous_const)
    have hJmopen : IsOpen Jm :=
      hDopen.preimage ((continuous_const.mul continuous_id).add continuous_const)
    have hJpimg : Jp = (fun u => 1 * u - T) '' D := by
      ext s
      constructor
      · intro hs
        change 1 * s + T ∈ D at hs
        refine ⟨1 * s + T, hs, ?_⟩
        change 1 * (1 * s + T) - T = s
        ring
      · rintro ⟨u, hu, rfl⟩
        change 1 * ((fun u => 1 * u - T) u) + T ∈ D
        have hrr : (1:ℝ) * (1 * u - T) + T = u := by ring
        rwa [hrr]
    have hJmimg : Jm = (fun u => 1 * u + T) '' D := by
      ext s
      constructor
      · intro hs
        change 1 * s + -T ∈ D at hs
        refine ⟨1 * s + -T, hs, ?_⟩
        change 1 * (1 * s + -T) + T = s
        ring
      · rintro ⟨u, hu, rfl⟩
        change 1 * ((fun u => 1 * u + T) u) + -T ∈ D
        have hrr : (1:ℝ) * (1 * u + T) + -T = u := by ring
        rwa [hrr]
    have hJpconn : Jp.OrdConnected :=
      isPreconnected_iff_ordConnected.mp (hJpimg ▸
        (hDconn.isPreconnected.image _
          (continuous_const.mul continuous_id |>.sub continuous_const).continuousOn))
    have hJmconn : Jm.OrdConnected :=
      isPreconnected_iff_ordConnected.mp (hJmimg ▸
        (hDconn.isPreconnected.image _
          (continuous_const.mul continuous_id |>.add continuous_const).continuousOn))
    have hδpunit : omIsUnitSpeedOn g dp Jp := hshift 1 T (mul_one 1) Jp dp hJpopen rfl rfl
    have hδmunit : omIsUnitSpeedOn g dm Jm := hshift 1 (-T) (mul_one 1) Jm dm hJmopen rfl rfl
    have h1t : (1:ℝ) * t1 + T = t2 := by rw [hTdef]; ring
    have h1tm : (1:ℝ) * t2 + -T = t1 := by rw [hTdef]; ring
    have htendp : Filter.Tendsto (fun s => 1 * s + T) (nhds t1) (nhds (1 * t1 + T)) :=
      ((continuous_const.mul continuous_id).add continuous_const).continuousAt.tendsto
    have htendm : Filter.Tendsto (fun s => 1 * s + -T) (nhds t2) (nhds (1 * t2 + -T)) :=
      ((continuous_const.mul continuous_id).add continuous_const).continuousAt.tendsto
    rw [h1t] at htendp
    rw [h1tm] at htendm
    have haffid : ∀ s, ε2 * (1 * s + T) + c2 = ε2 * s + c1 := by
      intro s
      linear_combination -hcenter + ε2 * hTdef
    have haffidm : ∀ s, ε2 * (1 * s + -T) + c1 = ε2 * s + c2 := by
      intro s
      linear_combination hcenter - ε2 * hTdef
    have hptp : ∀ s, (ε1 * s + c1 ∈ α.source ∧ γ s = α (ε1 * s + c1)) →
      (ε2 * (1 * s + T) + c2 ∈ α.source ∧
        γ (1 * s + T) = α (ε2 * (1 * s + T) + c2)) →
      dp s = γ s := by
      intro s h1 h2
      have e : ε2 * (1 * s + T) + c2 = ε1 * s + c1 := by
        rw [hεeq]; exact haffid s
      calc dp s = γ (1 * s + T) := rfl
        _ = α (ε2 * (1 * s + T) + c2) := h2.2
        _ = α (ε1 * s + c1) := by rw [e]
        _ = γ s := (h1.2).symm
    have hptm : ∀ s, (ε2 * s + c2 ∈ α.source ∧ γ s = α (ε2 * s + c2)) →
      (ε1 * (1 * s + -T) + c1 ∈ α.source ∧
        γ (1 * s + -T) = α (ε1 * (1 * s + -T) + c1)) →
      dm s = γ s := by
      intro s h2 h1
      have e : ε1 * (1 * s + -T) + c1 = ε2 * s + c2 := by
        rw [hεeq]; exact haffidm s
      calc dm s = γ (1 * s + -T) := rfl
        _ = α (ε1 * (1 * s + -T) + c1) := h1.2
        _ = α (ε2 * s + c2) := by rw [e]
        _ = γ s := (h2.2).symm
    have ht1Jp : t1 ∈ Jp := by
      change (1:ℝ) * t1 + T ∈ D
      rwa [h1t]
    have ht2Jm : t2 ∈ Jm := by
      change (1:ℝ) * t2 + -T ∈ D
      rwa [h1tm]
    have hevJp : dp =ᶠ[nhds t1] γ :=
      (hev1.and (htendp.eventually hev2)).mono fun s hs => hptp s hs.1 hs.2
    have hevJm : dm =ᶠ[nhds t2] γ :=
      (hev2.and (htendm.eventually hev1)).mono fun s hs => hptm s hs.1 hs.2
    obtain ⟨hJpsub, hEqp⟩ := om_maximal_unitSpeed_absorb g α0 D γ hprobe hmax Jp dp
      hJpopen hJpconn hδpunit t1 ⟨ht1, ht1Jp⟩ hevJp
    obtain ⟨hJmsub, -⟩ := om_maximal_unitSpeed_absorb g α0 D γ hprobe hmax Jm dm
      hJmopen hJmconn hδmunit t2 ⟨ht2, ht2Jm⟩ hevJm
    have hmem_add : ∀ s ∈ D, s + T ∈ D := by
      intro s hs
      apply hJmsub
      change 1 * (s + T) + -T ∈ D
      have hrr : (1:ℝ) * (s + T) + -T = s := by ring
      rwa [hrr]
    have hmem_sub : ∀ s ∈ D, s - T ∈ D := by
      intro s hs
      apply hJpsub
      change 1 * (s - T) + T ∈ D
      have hrr : (1:ℝ) * (s - T) + T = s := by ring
      rwa [hrr]
    have hN : ∀ n : ℕ, t1 + (n : ℝ) * T ∈ D := by
      intro n
      induction n with
      | zero =>
        have h0 : t1 + ((0 : ℕ) : ℝ) * T = t1 := by simp
        rwa [h0]
      | succ k ih =>
        have hkk : t1 + ((k + 1 : ℕ) : ℝ) * T = (t1 + (k : ℝ) * T) + T := by
          push_cast
          ring
        rw [hkk]
        exact hmem_add _ ih
    have hNm : ∀ n : ℕ, t1 - (n : ℝ) * T ∈ D := by
      intro n
      induction n with
      | zero =>
        have h0 : t1 - ((0 : ℕ) : ℝ) * T = t1 := by simp
        rwa [h0]
      | succ k ih =>
        have hkk : t1 - ((k + 1 : ℕ) : ℝ) * T = (t1 - (k : ℝ) * T) - T := by
          push_cast
          ring
        rw [hkk]
        exact hmem_sub _ ih
    have hDuniv : D = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro s
      obtain ⟨n, hn⟩ := exists_nat_gt ((s - t1) / T)
      obtain ⟨m', hm'⟩ := exists_nat_gt ((t1 - s) / T)
      have hn' : s < t1 + (n : ℝ) * T := by
        have h2 : s - t1 < (n : ℝ) * T := by
          rwa [div_lt_iff₀ hTpos] at hn
        linarith
      have hm'' : t1 - (m' : ℝ) * T < s := by
        have h2 : t1 - s < (m' : ℝ) * T := by
          rwa [div_lt_iff₀ hTpos] at hm'
        linarith
      exact hDconn.uIcc_subset (hNm m') (hN n)
        (Set.mem_uIcc_of_le (le_of_lt hm'') (le_of_lt hn'))
    have hJpuniv : Jp = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro s
      change (1:ℝ) * s + T ∈ D
      rw [hDuniv]
      exact Set.mem_univ _
    have hper1 : ∀ s, γ (1 * s + T) = γ s := by
      intro s
      have hsJ : s ∈ Jp := by rw [hJpuniv]; exact Set.mem_univ s
      exact hEqp hsJ
    refine ⟨hDuniv, fun s => ?_⟩
    calc γ (s + T) = γ (1 * s + T) := by rw [one_mul]
      _ = γ s := hper1 s
  · -- Reflection case: symmetry about the midpoint contradicts local injectivity.
    have hneg : ε1 = -ε2 := by
      obtain rfl | rfl <;> rcases hε2 with rfl | rfl := hε1
      · exact absurd rfl hεne
      · norm_num
      · norm_num
      · exact absurd rfl hεne
    set Lr : Set ℝ := (fun s => -1 * s + (t1 + t2)) ⁻¹' D
    set δr : ℝ → M := γ ∘ (fun s => -1 * s + (t1 + t2))
    have hLropen : IsOpen Lr :=
      hDopen.preimage ((continuous_const.mul continuous_id).add continuous_const)
    have hLrimg : Lr = (fun u => -1 * u + (t1 + t2)) '' D := by
      ext s
      constructor
      · intro hs
        change -1 * s + (t1 + t2) ∈ D at hs
        refine ⟨-1 * s + (t1 + t2), hs, ?_⟩
        change -1 * (-1 * s + (t1 + t2)) + (t1 + t2) = s
        ring
      · rintro ⟨u, hu, rfl⟩
        change -1 * ((fun u => -1 * u + (t1 + t2)) u) + (t1 + t2) ∈ D
        have hrr : (-1:ℝ) * (-1 * u + (t1 + t2)) + (t1 + t2) = u := by ring
        rwa [hrr]
    have hLrconn : Lr.OrdConnected :=
      isPreconnected_iff_ordConnected.mp (hLrimg ▸
        (hDconn.isPreconnected.image _
          (continuous_const.mul continuous_id |>.add continuous_const).continuousOn))
    have hneg11 : (-1:ℝ) * -1 = 1 := by rw [neg_mul_neg, mul_one]
    have hδrunit : omIsUnitSpeedOn g δr Lr :=
      hshift (-1) (t1 + t2) hneg11 Lr δr hLropen rfl rfl
    have h1tr : (-1:ℝ) * t1 + (t1 + t2) = t2 := by ring
    have htendr : Filter.Tendsto (fun s => -1 * s + (t1 + t2)) (nhds t1)
      (nhds (-1 * t1 + (t1 + t2))) :=
      ((continuous_const.mul continuous_id).add continuous_const).continuousAt.tendsto
    rw [h1tr] at htendr
    have ht1m : t1 + t2 - t1 = t2 := by ring
    have haffidr : ∀ s, ε2 * (-1 * s + (t1 + t2)) + c2 = ε1 * s + c1 := by
      intro s
      linear_combination -hcenter + (t1 - s) * hneg
    have hptr : ∀ s, (ε1 * s + c1 ∈ α.source ∧ γ s = α (ε1 * s + c1)) →
      (ε2 * (-1 * s + (t1 + t2)) + c2 ∈ α.source ∧
        γ (-1 * s + (t1 + t2)) = α (ε2 * (-1 * s + (t1 + t2)) + c2)) →
      δr s = γ s := by
      intro s h1 h2
      have e : ε2 * (-1 * s + (t1 + t2)) + c2 = ε1 * s + c1 := haffidr s
      calc δr s = γ (-1 * s + (t1 + t2)) := rfl
        _ = α (ε2 * (-1 * s + (t1 + t2)) + c2) := h2.2
        _ = α (ε1 * s + c1) := by rw [e]
        _ = γ s := (h1.2).symm
    have ht1Lr : t1 ∈ Lr := by
      change (-1:ℝ) * t1 + (t1 + t2) ∈ D
      rwa [h1tr]
    have hevr : δr =ᶠ[nhds t1] γ :=
      (hev1.and (htendr.eventually hev2)).mono fun s hs => hptr s hs.1 hs.2
    obtain ⟨-, hEqr⟩ := om_maximal_unitSpeed_absorb g α0 D γ hprobe hmax Lr δr
      hLropen hLrconn hδrunit t1 ⟨ht1, ht1Lr⟩ hevr
    set m : ℝ := (t1 + t2) / 2 with hmdef
    have hmuIcc : m ∈ Set.uIcc t1 t2 :=
      Set.mem_uIcc_of_le (by rw [hmdef]; linarith) (by rw [hmdef]; linarith)
    have hmD : m ∈ D := hDconn.uIcc_subset ht1 ht2 hmuIcc
    obtain ⟨ρ, hρpos, hρball⟩ := Metric.mem_nhds_iff.mp (hDopen.mem_nhds hmD)
    have hsym : ∀ w : ℝ, 0 < w → w < ρ → γ (m + w) = γ (m - w) := by
      intro w hw0 hwρ
      have hm1 : m + w ∈ D := by
        apply hρball
        rw [Metric.mem_ball, dist_eq_norm]
        have hrr : (m + w) - m = w := by ring
        rwa [hrr, Real.norm_eq_abs, abs_of_pos hw0]
      have hm2 : m - w ∈ D := by
        apply hρball
        rw [Metric.mem_ball, dist_eq_norm]
        have hrr : (m - w) - m = -w := by ring
        rw [hrr, Real.norm_eq_abs, abs_of_neg (by linarith)]
        linarith
      have hargw : t1 + t2 - (m + w) = m - w := by rw [hmdef]; ring
      have hLrw : m + w ∈ Lr := by
        change -1 * (m + w) + (t1 + t2) ∈ D
        rwa [show (-1:ℝ) * (m + w) + (t1 + t2) = m - w from by ring]
      have e : δr (m + w) = γ (m + w) := hEqr hLrw
      have e2 : δr (m + w) = γ (m - w) := by
        change γ (-1 * (m + w) + (t1 + t2)) = γ (m - w)
        rw [show (-1:ℝ) * (m + w) + (t1 + t2) = m - w from by ring]
      calc γ (m + w) = δr (m + w) := e.symm
        _ = γ (m - w) := e2
    obtain ⟨δ₀, hδ₀pos, hInj⟩ :=
      om_exists_injOn_of_unitSpeed g D γ hDopen hγunit m hmD
    set h : ℝ := min (δ₀ / 2) (ρ / 2) with hhdef
    have hhpos : 0 < h := lt_min (by linarith) (by linarith)
    have hδ : h < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hhρ : h < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hhm1 : m + h ∈ Set.Ioo (m - δ₀) (m + δ₀) :=
      Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    have hhm2 : m - h ∈ Set.Ioo (m - δ₀) (m + δ₀) :=
      Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    exfalso
    have hcontra := hInj hhm1 hhm2 (hsym h hhpos hhρ)
    have h0 : h = 0 := by linarith
    linarith

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

/--
[om_exists_minimal_period](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
generated by a minimal positive period. -/
private lemma om_exists_minimal_period
  (γ : ℝ → M) (δ : ℝ) (hδ : 0 < δ)
  (hinj : Set.InjOn γ (Set.Ioo (-δ) δ))
  (T : ℝ) (hT : T ≠ 0) (hperT : ∀ s, γ (s + T) = γ s)
  (hcoin : ∀ s t : ℝ, s ≠ t → γ s = γ t → ∀ u, γ (u + (t - s)) = γ u) :
  ∃ T0 : ℝ, 0 < T0 ∧ (∀ s, γ (s + T0) = γ s) ∧
    ∀ s t : ℝ, γ s = γ t ↔ ∃ n : ℤ, t - s = n * T0 := by
  have hadd : ∀ a b : ℝ, (∀ u, γ (u + a) = γ u) → (∀ u, γ (u + b) = γ u) →
    ∀ u, γ (u + (a + b)) = γ u := by
    intro a b ha hb u
    have h : u + (a + b) = (u + a) + b := by ring
    rw [h, hb, ha]
  have hneg : ∀ a : ℝ, (∀ u, γ (u + a) = γ u) → ∀ u, γ (u + -a) = γ u := by
    intro a ha u
    have h : u + -a + a = u := by ring
    have h2 := ha (u + -a)
    rwa [h] at h2
  set P : AddSubgroup ℝ :=
    { carrier := {T | ∀ u, γ (u + T) = γ u},
      add_mem' := fun {a b} ha hb => hadd a b ha hb,
      zero_mem' := fun u => by simp,
      neg_mem' := fun {a} ha => hneg a ha }
  have hTmem : T ∈ P := hperT
  have hdisc : ∀ x ∈ (P : Set ℝ), x ∈ Set.Ioo (-δ) δ → x = 0 := by
    intro x hxP hxI
    have hxP' : ∀ u, γ (u + x) = γ u := hxP
    have hx0 : γ x = γ 0 := by
      have h := hxP' 0
      rwa [zero_add] at h
    have hxI0 : (0:ℝ) ∈ Set.Ioo (-δ) δ :=
      Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    exact hinj hxI hxI0 hx0
  have hndense : ¬ Dense (P : Set ℝ) := by
    intro hd
    obtain ⟨x, hxP, hxI⟩ := hd.exists_between (show (0:ℝ) < δ from hδ)
    obtain ⟨hx0', -⟩ := Set.mem_Ioo.mp hxI
    have hxI' : x ∈ Set.Ioo (-δ) δ := by
      obtain ⟨hx0'', hxδ⟩ := Set.mem_Ioo.mp hxI
      exact Set.mem_Ioo.mpr ⟨by linarith, hxδ⟩
    have hx0 := hdisc x hxP hxI'
    linarith
  obtain ⟨a, ha⟩ := (AddSubgroup.dense_or_cyclic P).resolve_left hndense
  have ha0 : a ≠ 0 := by
    intro h0
    have hTmem' : T ∈ AddSubgroup.closure ({a} : Set ℝ) := by
      rwa [← ha]
    obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp hTmem'
    rw [h0, smul_zero] at hn
    exact hT hn.symm
  set T0 : ℝ := |a| with hT0def
  have hT0pos : 0 < T0 := abs_pos.mpr ha0
  have haP : a ∈ P := by
    rw [ha]
    exact AddSubgroup.mem_closure_singleton_self a
  have hper_a : ∀ s, γ (s + a) = γ s := haP
  have hper_neg : ∀ s, γ (s + -a) = γ s := P.neg_mem haP
  have hper0 : ∀ s, γ (s + T0) = γ s := by
    obtain ha' | ha' := lt_or_gt_of_ne ha0
    · have hT0a : T0 = -a := abs_of_neg ha'
      intro s
      rw [hT0a]
      exact hper_neg s
    · have hT0a : T0 = a := abs_of_nonneg (le_of_lt ha')
      intro s
      rw [hT0a]
      exact hper_a s
  have hiff : ∀ s t : ℝ, γ s = γ t ↔ ∃ n : ℤ, t - s = n * T0 := by
    intro s t
    constructor
    · intro hst
      by_cases hst' : s = t
      · refine ⟨0, ?_⟩
        rw [hst']
        simp
      · have hmem : t - s ∈ P := hcoin s t hst' hst
        have hmem' : t - s ∈ AddSubgroup.closure ({a} : Set ℝ) := by
          rwa [← ha]
        obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp hmem'
        obtain ha' | ha' := lt_or_gt_of_ne ha0
        · refine ⟨-n, ?_⟩
          have hT0a : T0 = -a := abs_of_neg ha'
          have hnn : (((-n : ℤ)) : ℝ) * -a = (n : ℝ) * a := by
            push_cast
            ring
          rw [hT0a, hnn, ← hn]
          exact zsmul_eq_mul _ _
        · refine ⟨n, ?_⟩
          have hT0a : T0 = a := abs_of_nonneg (le_of_lt ha')
          rw [hT0a, ← hn]
          exact zsmul_eq_mul _ _
    · intro hnt
      obtain ⟨n, hn⟩ := hnt
      have hper : Function.Periodic γ T0 := hper0
      have hstep := (hper.int_mul n) s
      have ht : t = s + (n : ℝ) * T0 := by linarith
      rwa [ht]
  exact ⟨T0, hT0pos, hper0, hiff⟩

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

/--
[om_isLocalDiffeomorph_circleExp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
the map `θ ↦ Circle.exp θ` on `Ioo (θ₀ - π) (θ₀ + π)` has the smooth local inverse
`z ↦ θ₀ + arg (z * w⁻¹)` on the preimage of the slit plane; smoothness of the
inverse goes through the complex logarithm. -/
private lemma om_isLocalDiffeomorph_circleExp :
  IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞ ⇑Circle.exp := by
  intro θ₀
  have := finrank_real_complex_fact'
  set w : Circle := Circle.exp θ₀ with hw
  set f₁ : Circle → ℂ := fun z => ((z * w⁻¹ : Circle) : ℂ) with hf₁
  set U : Set ℝ := Set.Ioo (θ₀ - Real.pi) (θ₀ + Real.pi) with hU
  set V : Set Circle := f₁ ⁻¹' Complex.slitPlane with hV
  set L : Circle → ℝ := fun z => θ₀ + Complex.arg (f₁ z) with hL
  have hUopen : IsOpen U := isOpen_Ioo
  have hU0 : θ₀ ∈ U := Set.mem_Ioo.mpr
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hmulW : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle => z * w⁻¹) :=
    contMDiff_mul_right
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) :=
    contMDiff_coe_sphere
  have hinner : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ f₁ := hcoe.comp hmulW
  have hf₁cont : Continuous f₁ := hinner.continuous
  have hVopen : IsOpen V := Complex.isOpen_slitPlane.preimage hf₁cont
  have hED : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ ⇑Circle.exp U :=
    (contMDiff_circleExp : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ ⇑Circle.exp).contMDiffOn.mono
      (Set.subset_univ _)
  have hexpsub : ∀ θ : ℝ, Circle.exp θ * w⁻¹ = Circle.exp (θ - θ₀) := by
    intro θ
    rw [hw, ← div_eq_mul_inv, ← Circle.exp_sub]
  have hsubmem : ∀ θ ∈ U, θ - θ₀ ∈ Set.Ioo (-Real.pi) Real.pi := by
    intro θ hθ
    have hθI : θ ∈ Set.Ioo (θ₀ - Real.pi) (θ₀ + Real.pi) := hθ
    have hθII := Set.mem_Ioo.mp hθI
    rw [Set.mem_Ioo]
    constructor <;> linarith
  have hce : ∀ θ ∈ U, f₁ (Circle.exp θ) = ((Circle.exp (θ - θ₀) : Circle) : ℂ) := by
    intro θ hθ
    change ((Circle.exp θ * w⁻¹ : Circle) : ℂ) = _
    rw [hexpsub θ]
  have hargC : ∀ θ ∈ U, Complex.arg (((Circle.exp (θ - θ₀) : Circle)) : ℂ)
    = θ - θ₀ := by
    intro θ hθ
    have hmemI := Set.mem_Ioo.mp (hsubmem θ hθ)
    exact Circle.arg_exp hmemI.1 (le_of_lt hmemI.2)
  have hMapsE : Set.MapsTo ⇑Circle.exp U V := by
    intro θ hθ
    have hzmem : f₁ (Circle.exp θ) ∈ Complex.slitPlane := by
      rw [hce θ hθ, Complex.mem_slitPlane_iff_arg]
      have hmemI := Set.mem_Ioo.mp (hsubmem θ hθ)
      rw [hargC θ hθ]
      exact ⟨ne_of_lt hmemI.2, Circle.coe_ne_zero _⟩
    exact hzmem
  have hLeft : ∀ θ ∈ U, L (Circle.exp θ) = θ := by
    intro θ hθ
    have hmemI := Set.mem_Ioo.mp (hsubmem θ hθ)
    have h1 : L (Circle.exp θ) = θ₀ + (θ - θ₀) := by
      change θ₀ + Complex.arg (f₁ (Circle.exp θ)) = _
      rw [hce θ hθ, Circle.arg_exp hmemI.1 (le_of_lt hmemI.2)]
    rw [h1]
    ring
  have hRight : ∀ z ∈ V, Circle.exp (L z) = z := by
    intro z hz
    have h1 : L z = θ₀ + Complex.arg (((z * w⁻¹ : Circle)) : ℂ) := rfl
    rw [h1, Circle.exp_add, ← hw, Circle.exp_arg]
    change w * (z * w⁻¹) = z
    rw [mul_left_comm, mul_inv_cancel, mul_one]
  have hMapsL : Set.MapsTo L V U := by
    intro z hz
    have hzmem : f₁ z ∈ Complex.slitPlane := hz
    have hne : Complex.arg (f₁ z) ≠ Real.pi :=
      (Complex.mem_slitPlane_iff_arg.mp hzmem).1
    have hlt : Complex.arg (f₁ z) < Real.pi := by
      obtain h | h := lt_or_eq_of_le (Complex.arg_le_pi _)
      · exact h
      · exact absurd h hne
    have hgt : -Real.pi < Complex.arg (f₁ z) := Complex.neg_pi_lt_arg _
    have hmem : L z ∈ Set.Ioo (θ₀ - Real.pi) (θ₀ + Real.pi) := by
      rw [Set.mem_Ioo]
      change θ₀ - Real.pi < θ₀ + Complex.arg (f₁ z) ∧
        θ₀ + Complex.arg (f₁ z) < θ₀ + Real.pi
      constructor <;> linarith
    exact hmem
  have houter : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
    (fun c : ℂ => θ₀ + Complex.arg c) Complex.slitPlane := by
    have hlog : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
      (fun c : ℂ => θ₀ + (Complex.log c).im) Complex.slitPlane := by
      rw [contMDiffOn_iff_contDiffOn]
      intro c hc
      have h1 : ContDiffAt ℂ ∞ Complex.log c := Complex.contDiffAt_log hc
      have h2 : ContDiffAt ℝ ∞ Complex.log c := h1.restrict_scalars (𝕜 := ℝ)
      have h3' : ContDiffAt ℝ ∞ (fun c : ℂ => (Complex.log c).im) c :=
        (Complex.imCLM.contDiff.contDiffAt).comp c h2
      have h4 : ContDiffAt ℝ ∞ (fun c : ℂ => θ₀ + (Complex.log c).im) c :=
        contDiffAt_const.add h3'
      exact h4.contDiffWithinAt
    refine hlog.congr (fun c hc => ?_)
    show θ₀ + Complex.arg c = θ₀ + (Complex.log c).im
    rw [Complex.log_im]
  have hLD : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ L V := by
    have hinnerV : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℂ) ∞ f₁ V :=
      hinner.contMDiffOn.mono (Set.subset_univ _)
    have hcomp := houter.comp hinnerV (fun z hz => hz)
    exact hcomp.congr (fun z hz => rfl)
  exact odm_isLocalDiffeomorphAt_of_invOn ⇑Circle.exp L U V hUopen hVopen
    hMapsE hMapsL ⟨hLeft, hRight⟩ hED hLD θ₀ hU0

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
/--
[om_nonempty_diffeomorph_circle_of_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
whose coincidence set is exactly the lattice `T₀·ℤ` descends to a diffeomorphism
from `Circle`, via `z ↦ γ ((T₀/(2π)) * arg z)`. -/
private lemma om_nonempty_diffeomorph_circle_of_periodic
  (γ : ℝ → M) (hsurj : Function.Surjective γ)
  (hld : ∀ t : ℝ, IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ t)
  (T₀ : ℝ) (hT₀ : 0 < T₀)
  (hiff : ∀ s t : ℝ, γ s = γ t ↔ ∃ n : ℤ, t - s = n * T₀) :
  Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ M) := by
  have hT₀ne : T₀ ≠ 0 := ne_of_gt hT₀
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have h2pi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero hpi
  have hperInt : ∀ (s : ℝ) (m : ℤ), γ (s + m * T₀) = γ s := by
    intro s m
    exact ((hiff s (s + m * T₀)).mpr ⟨m, by ring⟩).symm
  set c : ℝ := T₀ / (2 * Real.pi) with hc
  set G : Circle → M := fun z => γ (c * Complex.arg (z : ℂ)) with hG
  have hcc : (2 * Real.pi / T₀) * (T₀ / (2 * Real.pi)) = 1 := by
    rw [div_mul_div_comm, mul_comm T₀,
      div_self (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hT₀ne)]
  have hGexp : ∀ θ : ℝ, G (Circle.exp θ) = γ (c * θ) := by
    intro θ
    have harg : Circle.exp (Complex.arg ((Circle.exp θ : Circle) : ℂ))
      = Circle.exp θ :=
      Circle.exp_arg _
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp harg
    have hscale : c * Complex.arg ((Circle.exp θ : Circle) : ℂ)
      = c * θ + m * T₀ := by
      rw [hm, mul_add]
      congr 1
      rw [hc, mul_left_comm, div_mul_cancel₀ _ h2pi]
    have hGθ : G (Circle.exp θ)
      = γ (c * Complex.arg ((Circle.exp θ : Circle) : ℂ)) := rfl
    rw [hGθ, hscale]
    exact hperInt _ m
  have hGsurj : Function.Surjective G := by
    intro y
    obtain ⟨t, rfl⟩ := hsurj y
    refine ⟨Circle.exp (2 * Real.pi * t / T₀), ?_⟩
    rw [hGexp]
    have e : c * (2 * Real.pi * t / T₀) = t := by
      rw [hc]
      field_simp
    rw [e]
  have hGinj : Function.Injective G := by
    intro z₁ z₂ h
    have hγ : γ (c * Complex.arg (z₁ : ℂ)) = γ (c * Complex.arg (z₂ : ℂ)) := h
    obtain ⟨n, hn⟩ := (hiff _ _).mp hγ
    have hdiff : Complex.arg (z₂ : ℂ) - Complex.arg (z₁ : ℂ)
      = ↑n * (2 * Real.pi) := by
      have e : c * (Complex.arg (z₂ : ℂ) - Complex.arg (z₁ : ℂ)) = ↑n * T₀ := by
        rwa [mul_sub]
      have hT : (2 * Real.pi / T₀) * (c * (Complex.arg (z₂ : ℂ) - Complex.arg (z₁ : ℂ)))
        = (2 * Real.pi / T₀) * (↑n * T₀) := congrArg _ e
      have hL : (2 * Real.pi / T₀) * (c * (Complex.arg (z₂ : ℂ) - Complex.arg (z₁ : ℂ)))
        = Complex.arg (z₂ : ℂ) - Complex.arg (z₁ : ℂ) := by
        rw [hc, ← mul_assoc, hcc, one_mul]
      have hR : (2 * Real.pi / T₀) * (↑n * T₀) = ↑n * (2 * Real.pi) := by
        rw [mul_left_comm, div_mul_cancel₀ _ hT₀ne]
      rwa [hL, hR] at hT
    have e1 : Circle.exp (Complex.arg (z₁ : ℂ)) = z₁ := Circle.exp_arg z₁
    have e2 : Circle.exp (Complex.arg (z₂ : ℂ)) = z₂ := Circle.exp_arg z₂
    have harg2 : Complex.arg (z₂ : ℂ)
      = Complex.arg (z₁ : ℂ) + ↑n * (2 * Real.pi) := by linarith [hdiff]
    rw [← e1, ← e2, harg2, Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
  have hGl : IsLocalDiffeomorph (𝓡 1) (𝓡 1) ∞ G := by
    intro z
    have hθ : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ ⇑Circle.exp
      (Complex.arg (z : ℂ)) :=
      om_isLocalDiffeomorph_circleExp _
    set ψ : Circle → ℝ := ⇑hθ.localInverse with hψ
    have hψl : IsLocalDiffeomorphAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ ψ
      (⇑Circle.exp (Complex.arg (z : ℂ))) :=
      hθ.localInverse_isLocalDiffeomorphAt
    have hze : ⇑Circle.exp (Complex.arg (z : ℂ)) = z := Circle.exp_arg z
    rw [hze] at hψl
    set sc : ℝ → ℝ := fun t => c * t with hsc
    set iv : ℝ → ℝ := fun s => (2 * Real.pi / T₀) * s with hiv
    have hscD : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ sc Set.univ :=
      (contDiff_const.mul contDiff_id).contMDiff.contMDiffOn
    have hivD : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ iv Set.univ :=
      (contDiff_const.mul contDiff_id).contMDiff.contMDiffOn
    have hleft : ∀ x ∈ (Set.univ : Set ℝ), iv (sc x) = x := by
      intro x _
      change (2 * Real.pi / T₀) * (c * x) = x
      rw [← mul_assoc, hc, hcc, one_mul]
    have hright : ∀ y ∈ (Set.univ : Set ℝ), sc (iv y) = y := by
      intro y _
      change c * ((2 * Real.pi / T₀) * y) = y
      rw [← mul_assoc]
      have hcc₂ : c * (2 * Real.pi / T₀) = 1 := by
        rw [hc, div_mul_div_comm, mul_comm T₀,
          div_self (mul_ne_zero h2pi hT₀ne)]
      rw [hcc₂, one_mul]
    have hsc_ld : ∀ t' : ℝ, IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ sc t' := by
      intro t'
      exact odm_isLocalDiffeomorphAt_of_invOn sc iv Set.univ Set.univ
        isOpen_univ isOpen_univ (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
        ⟨hleft, hright⟩ hscD hivD t' (Set.mem_univ _)
    have hγsc : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ (sc (ψ z)) := hld _
    have hmid : IsLocalDiffeomorphAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ (sc ∘ ψ) z :=
      IsLocalDiffeomorphAt.comp (K := 𝓘(ℝ, ℝ)) (P := ℝ) hψl (hsc_ld _)
    have hcomp : IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ ((γ ∘ sc) ∘ ψ) z :=
      IsLocalDiffeomorphAt.comp (K := 𝓡 1) (P := M) hmid hγsc
    have hGeq : G =ᶠ[nhds z] ((γ ∘ sc) ∘ ψ) := by
      have hbase := hθ.localInverse_eventuallyEq_right
      rw [hze] at hbase
      filter_upwards [hbase] with z' hz'
      change G z' = γ (sc (ψ z'))
      have e1 : G z' = G (⇑Circle.exp (ψ z')) := by
        congr 1
        exact hz'.symm
      rw [e1, hGexp]
    exact odm_isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp hGeq
  exact ⟨hGl.diffeomorphOfBijective ⟨hGinj, hGsurj⟩⟩
section BoundaryInterior
variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  [IsManifold (𝓡∂ 1) ∞ M]

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
/--
[omb_chartAt_ombInterior](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_chartAt_ombInterior (x : ↥(ombInterior M)) :
  chartAt (EuclideanSpace ℝ (Fin 1)) x =
    (chartAt (EuclideanHalfSpace 1) x).trans omb_interiorModelHomeomorph :=
  rfl

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
/--
[ombRetract_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma ombRetract_of_mem (x₀ : ↥(ombInterior M)) (y : M)
  (h : y ∈ ombInterior M) : ombRetract M x₀ y = ⟨y, h⟩ := by
  unfold ombRetract
  split
  · rfl
  · next h' => exact (h' h).elim

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
/--
[omb_contMDiffOn_val_of_mem_chartAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_contMDiffOn_val_of_mem_chartAt (x : ↥(ombInterior M)) :
  ContMDiffOn (𝓡 1) (𝓡∂ 1) ∞ (Subtype.val : ↥(ombInterior M) → M)
    ((chartAt (EuclideanSpace ℝ (Fin 1)) x).source) := by
  have he : (chartAt (EuclideanSpace ℝ (Fin 1)) x) ∈
    IsManifold.maximalAtlas (𝓡 1) ∞ ↥(ombInterior M) :=
    IsManifold.chart_mem_maximalAtlas x
  have he' : (chartAt (EuclideanHalfSpace 1) (x.val)) ∈
    IsManifold.maximalAtlas (𝓡∂ 1) ∞ M :=
    IsManifold.chart_mem_maximalAtlas (x.val)
  have h2s : Set.MapsTo (Subtype.val : ↥(ombInterior M) → M)
    ((chartAt (EuclideanSpace ℝ (Fin 1)) x).source)
    ((chartAt (EuclideanHalfSpace 1) (x.val)).source) := by
    intro w hw
    rw [omb_chartAt_ombInterior, OpenPartialHomeomorph.trans_source] at hw
    obtain ⟨hwA, -⟩ := hw
    rwa [TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] at hwA
  rw [contMDiffOn_iff_of_mem_maximalAtlas he he' (fun x hx => hx) h2s]
  refine ⟨continuous_subtype_val.continuousOn, ?_⟩
  have hEq : Set.EqOn (((chartAt (EuclideanHalfSpace 1) (x.val)).extend (𝓡∂ 1)) ∘
    (Subtype.val : ↥(ombInterior M) → M) ∘
    ((chartAt (EuclideanSpace ℝ (Fin 1)) x).extend (𝓡 1)).symm) id
    (((chartAt (EuclideanSpace ℝ (Fin 1)) x).extend (𝓡 1)) ''
      ((chartAt (EuclideanSpace ℝ (Fin 1)) x).source)) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hleft : ((chartAt (EuclideanSpace ℝ (Fin 1)) x).extend (𝓡 1)).symm
      (((chartAt (EuclideanSpace ℝ (Fin 1)) x).extend (𝓡 1)) w) = w :=
      ((chartAt (EuclideanSpace ℝ (Fin 1)) x).extend (𝓡 1)).left_inv (by
        rwa [OpenPartialHomeomorph.extend_source])
    simp only [Function.comp_apply, hleft]
    rfl
  exact contDiffOn_id.congr hEq

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
/--
[omb_contMDiffOn_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_contMDiffOn_val :
  ContMDiffOn (𝓡 1) (𝓡∂ 1) ∞ (Subtype.val : ↥(ombInterior M) → M)
    Set.univ := by
  intro x _
  have hW := omb_contMDiffOn_val_of_mem_chartAt M x
  have hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) x).source :=
    mem_chart_source _ x
  have hxnhds : (chartAt (EuclideanSpace ℝ (Fin 1)) x).source ∈ nhds x :=
    (chartAt (EuclideanSpace ℝ (Fin 1)) x).open_source.mem_nhds hx
  exact (hW.contMDiffAt hxnhds).contMDiffWithinAt

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
/--
[omb_coord_pos_of_mem_source](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_coord_pos_of_mem_source (y₀ y : M)
  (hy : y ∈ (chartAt (EuclideanHalfSpace 1) y₀).source)
  (hint : (𝓡∂ 1).IsInteriorPoint y) :
  0 < (((chartAt (EuclideanHalfSpace 1) y₀) y).val).ofLp 0 := by
  have h1 := (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (n := ∞)
    (by simp : (∞ : ℕ∞ω) ≠ 0) (chart_mem_atlas _ y₀) hy).mp hint
  have h2 := OpenPartialHomeomorph.interior_extend_target_subset_interior_range
    (f := chartAt (EuclideanHalfSpace 1) y₀) (I := (𝓡∂ 1)) h1
  rw [interior_range_modelWithCornersEuclideanHalfSpace 1] at h2
  have h3 : 0 < ((𝓡∂ 1) ((chartAt (EuclideanHalfSpace 1) y₀) y)).ofLp 0 := h2
  have h4 : (𝓡∂ 1) ((chartAt (EuclideanHalfSpace 1) y₀) y) =
    (((chartAt (EuclideanHalfSpace 1) y₀) y).val :
      EuclideanSpace ℝ (Fin 1)) := rfl
  rwa [h4] at h3

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
/--
[omb_opens_chartAt_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_opens_chartAt_apply (u w : ↥(ombInterior M)) :
  (chartAt (EuclideanHalfSpace 1) u) w =
    (chartAt (EuclideanHalfSpace 1) (u.val)) (w.val) :=
  rfl

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
/--
[omb_contMDiffOn_retract_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_contMDiffOn_retract_of_mem (x₀ : ↥(ombInterior M)) (y : M)
  (hy : y ∈ (ombInterior M : Set M)) :
  ContMDiffOn (𝓡∂ 1) (𝓡 1) ∞ (ombRetract M x₀)
    ((chartAt (EuclideanHalfSpace 1) y).source ∩ ↑(ombInterior M)) := by
  have hyO : y ∈ ombInterior M := SetLike.mem_coe.mp hy
  have he : (chartAt (EuclideanHalfSpace 1) y) ∈
    IsManifold.maximalAtlas (𝓡∂ 1) ∞ M :=
    IsManifold.chart_mem_maximalAtlas y
  have he' : (chartAt (EuclideanSpace ℝ (Fin 1)) (⟨y, hyO⟩ : ↥(ombInterior M))) ∈
    IsManifold.maximalAtlas (𝓡 1) ∞ ↥(ombInterior M) :=
    IsManifold.chart_mem_maximalAtlas _
  have h2s : Set.MapsTo (ombRetract M x₀)
    ((chartAt (EuclideanHalfSpace 1) y).source ∩ ↑(ombInterior M))
    ((chartAt (EuclideanSpace ℝ (Fin 1)) (⟨y, hyO⟩ : ↥(ombInterior M))).source) := by
    intro w hw
    obtain ⟨hwA, hwS⟩ := hw
    have hwO : w ∈ ombInterior M := SetLike.mem_coe.mp hwS
    rw [ombRetract_of_mem M x₀ w hwO, omb_chartAt_ombInterior,
      OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage]
      exact hwA
    · rw [Set.mem_preimage, omb_opens_chartAt_apply]
      have hpos := omb_coord_pos_of_mem_source M y w hwA hwO
      exact hpos
  rw [contMDiffOn_iff_of_mem_maximalAtlas' he he' Set.inter_subset_left h2s]
  have hEq : Set.EqOn (((chartAt (EuclideanSpace ℝ (Fin 1))
    (⟨y, hyO⟩ : ↥(ombInterior M))).extend (𝓡 1)) ∘ (ombRetract M x₀) ∘
    ((chartAt (EuclideanHalfSpace 1) y).extend (𝓡∂ 1)).symm) id
    (((chartAt (EuclideanHalfSpace 1) y).extend (𝓡∂ 1)) ''
      ((chartAt (EuclideanHalfSpace 1) y).source ∩ ↑(ombInterior M))) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨hwA, hwS⟩ := hw
    have hwO : w ∈ ombInterior M := SetLike.mem_coe.mp hwS
    have hleft : ((chartAt (EuclideanHalfSpace 1) y).extend (𝓡∂ 1)).symm
      (((chartAt (EuclideanHalfSpace 1) y).extend (𝓡∂ 1)) w) = w :=
      ((chartAt (EuclideanHalfSpace 1) y).extend (𝓡∂ 1)).left_inv (by
        rwa [OpenPartialHomeomorph.extend_source])
    simp only [Function.comp_apply, hleft, ombRetract_of_mem M x₀ w hwO]
    rfl
  exact contDiffOn_id.congr hEq

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
/--
[omb_contMDiffOn_retract](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_contMDiffOn_retract (x₀ : ↥(ombInterior M)) :
  ContMDiffOn (𝓡∂ 1) (𝓡 1) ∞ (ombRetract M x₀) ↑(ombInterior M) := by
  intro y hy
  have hW := omb_contMDiffOn_retract_of_mem M x₀ y hy
  have hymem : y ∈ (chartAt (EuclideanHalfSpace 1) y).source ∩
    ↑(ombInterior M) :=
    ⟨mem_chart_source _ y, hy⟩
  have hynnhds : (chartAt (EuclideanHalfSpace 1) y).source ∩
    ↑(ombInterior M) ∈ nhds y :=
    Filter.inter_mem ((chartAt (EuclideanHalfSpace 1) y).open_source.mem_nhds
      (mem_chart_source _ y)) ((ombInterior M).2.mem_nhds
        (SetLike.mem_coe.mp hy))
  exact (hW.contMDiffAt hynnhds).contMDiffWithinAt

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
/--
[omb_exists_partialDiffeomorph_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_exists_partialDiffeomorph_val (x₀ : ↥(ombInterior M)) :
  ∃ Φ : PartialDiffeomorph (𝓡 1) (𝓡∂ 1) ↥(ombInterior M) M ∞,
    Φ.source = Set.univ ∧ Φ.target = ↑(ombInterior M) ∧
      (⇑Φ : ↥(ombInterior M) → M) = Subtype.val ∧
      Set.EqOn ⇑Φ.symm (ombRetract M x₀) ↑(ombInterior M) := by
  have hf : Set.MapsTo (Subtype.val : ↥(ombInterior M) → M) Set.univ
    ↑(ombInterior M) := fun x _ => x.2
  have hf' : Set.MapsTo (ombRetract M x₀) ↑(ombInterior M) Set.univ :=
    Set.mapsTo_univ _ _
  have hInv : Set.InvOn (ombRetract M x₀)
    (Subtype.val : ↥(ombInterior M) → M) Set.univ ↑(ombInterior M) := by
    refine ⟨?_, ?_⟩
    · intro x _
      rw [ombRetract_of_mem M x₀ _ x.2]
    · intro y hy
      have hyO : y ∈ ombInterior M := SetLike.mem_coe.mp hy
      rw [ombRetract_of_mem M x₀ y hyO]
  exact odm_exists_partialDiffeomorph_of_invOn _ _ _ _ isOpen_univ
    (ombInterior M).2 hf hf' hInv (omb_contMDiffOn_val M)
    (omb_contMDiffOn_retract M x₀)

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
/--
[omb_isLocalDiffeomorph_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_isLocalDiffeomorph_val (x₀ : ↥(ombInterior M)) :
  IsLocalDiffeomorph (𝓡 1) (𝓡∂ 1) ∞
    (Subtype.val : ↥(ombInterior M) → M) := by
  obtain ⟨Φ, hsrc, -, hfun, -⟩ := omb_exists_partialDiffeomorph_val M x₀
  intro x
  have hx : x ∈ Φ.source := by rw [hsrc]; exact Set.mem_univ x
  have h := PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 1) (𝓡∂ 1) ∞ Φ hx
  rwa [hfun] at h

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
/--
[omb_isLocalDiffeomorphAt_retract](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_isLocalDiffeomorphAt_retract (x₀ : ↥(ombInterior M))
  (y : M) (hy : y ∈ (ombInterior M : Set M)) :
  IsLocalDiffeomorphAt (𝓡∂ 1) (𝓡 1) ∞ (ombRetract M x₀) y := by
  have hf : Set.MapsTo (ombRetract M x₀) ↑(ombInterior M) Set.univ :=
    Set.mapsTo_univ _ _
  have hf' : Set.MapsTo (Subtype.val : ↥(ombInterior M) → M) Set.univ
    ↑(ombInterior M) := fun x _ => x.2
  have hInv : Set.InvOn (Subtype.val : ↥(ombInterior M) → M)
    (ombRetract M x₀) ↑(ombInterior M) Set.univ := by
    refine ⟨?_, ?_⟩
    · intro z hz
      have hzO : z ∈ ombInterior M := SetLike.mem_coe.mp hz
      rw [ombRetract_of_mem M x₀ z hzO]
    · intro x _
      rw [ombRetract_of_mem M x₀ _ x.2]
  exact odm_isLocalDiffeomorphAt_of_invOn _ _ _ _ (ombInterior M).2 isOpen_univ
    hf hf' hInv (omb_contMDiffOn_retract M x₀) (omb_contMDiffOn_val M) y hy

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
/--
[omb_halfCurve_V_open](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
omit [IsManifold (𝓡∂ 1) ∞ M] in
private lemma omb_halfCurve_V_open (p : M) (ε : ℝ) :
  IsOpen ((chartAt (EuclideanHalfSpace 1) p).source ∩
    (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
      {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) := by
  apply (chartAt (EuclideanHalfSpace 1) p).isOpen_inter_preimage
  have hcont : Continuous (fun y : EuclideanHalfSpace 1 => (y.val) 0) :=
    (PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val
  have : {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε} =
    (fun y : EuclideanHalfSpace 1 => (y.val) 0) ⁻¹' Set.Ioo 0 ε := rfl
  rw [this]
  exact isOpen_Ioo.preimage hcont

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
/--
[omb_halfCurveInv_contMDiffOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_halfCurveInv_contMDiffOn (p : M) (ε : ℝ) :
  ContMDiffOn (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (ombHalfCurveInv M p)
    ((chartAt (EuclideanHalfSpace 1) p).source ∩
      (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
        {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) := by
  have he : ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞
    (chartAt (EuclideanHalfSpace 1) p)
    (chartAt (EuclideanHalfSpace 1) p).source :=
    contMDiffOn_chart
  have heV : ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞
    (chartAt (EuclideanHalfSpace 1) p)
    ((chartAt (EuclideanHalfSpace 1) p).source ∩
      (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
        {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) :=
    he.mono Set.inter_subset_left
  have hI : ContMDiff (𝓡∂ 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞ (𝓡∂ 1) :=
    (𝓡∂ 1).contMDiff
  have hIe : ContMDiffOn (𝓡∂ 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞
    ((𝓡∂ 1) ∘ (chartAt (EuclideanHalfSpace 1) p))
    ((chartAt (EuclideanHalfSpace 1) p).source ∩
      (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
        {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) :=
    hI.contMDiffOn.comp heV Set.subset_preimage_univ
  have hL : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℝ) ∞
    omLinEquiv.symm :=
    contMDiff_iff_contDiff.mpr omLinEquiv.symm.contDiff
  have hfin : ContMDiffOn (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞
    (omLinEquiv.symm ∘ ((𝓡∂ 1) ∘ (chartAt (EuclideanHalfSpace 1) p)))
    ((chartAt (EuclideanHalfSpace 1) p).source ∩
      (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
        {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) :=
    hL.contMDiffOn.comp hIe Set.subset_preimage_univ
  have heq : ombHalfCurveInv M p =
    omLinEquiv.symm ∘ ((𝓡∂ 1) ∘ (chartAt (EuclideanHalfSpace 1) p)) := rfl
  rwa [heq]

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[connected_boundaryless_one_manifold_classification](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
lemma connected_boundaryless_one_manifold_classification
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] :
-- imply
  Nonempty (M ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) ∨ Nonempty (M ≃ₘ⟮𝓡 1, 𝓡 1⟯ (EuclideanSpace ℝ (Fin 1))) := by
-- proof
  classical
  obtain ⟨g⟩ := om_riemannianMetric (M := M)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  obtain ⟨α₀, hα₀src, hα₀₀, _, hα₀speed⟩ := om_exists_unitSpeedChart g x₀
  obtain ⟨D, γ, hDadm, hmax⟩ :=
    om_exists_maximal_unitSpeed g α₀ hα₀src hα₀₀ hα₀speed
  have hDadmC := hDadm
  obtain ⟨hDopen, hDconn, h0D, hγunit, _⟩ := hDadmC
  have himg : γ '' D = Set.univ :=
    om_maximal_unitSpeed_image_eq_univ g α₀ D γ hDadm hmax
  by_cases hInj : Set.InjOn γ D
  · -- Injective case: `M` is diffeomorphic to `E1`, via `γ ∘ φ`.
    obtain ⟨φ, hφsmooth, hφderiv, hφrange⟩ :=
      odm_exists_contDiff_deriv_pos_range_eq D hDopen hDconn ⟨0, h0D⟩
    have hφD : ContDiffOn ℝ ∞ φ Set.univ := hφsmooth.contDiffOn
    have hderivU : ∀ t ∈ (Set.univ : Set ℝ), 0 < deriv φ t :=
      fun t _ => hφderiv t
    obtain ⟨Φ, hΦsrc, hΦfun, _, _, _⟩ :=
      odm_exists_partialDiffeomorph_of_deriv_pos Set.univ φ isOpen_univ
        (isPreconnected_iff_ordConnected.mp isPreconnected_univ) hφD hderivU
    have hFld : IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞ (γ ∘ φ) := by
      intro t
      have hmem : φ t ∈ D := hφrange ▸ Set.mem_range_self t
      have hγt := om_isLocalDiffeomorphAt_of_unitSpeed g D γ hDopen hγunit
        (φ t) hmem
      have hφt : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ φ t := by
        have hmemS : t ∈ Φ.source := by
          rw [hΦsrc]
          exact Set.mem_univ t
        have h := PartialDiffeomorph.isLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
          Φ hmemS
        rwa [hΦfun] at h
      exact IsLocalDiffeomorphAt.comp (K := 𝓡 1) (P := M) hφt hγt
    have hφinj : Function.Injective φ := by
      have hstrict : StrictMonoOn φ Set.univ :=
        strictMonoOn_of_deriv_pos convex_univ hφD.continuousOn (by
          rw [isOpen_univ.interior_eq]
          exact hderivU)
      intro a b hab
      obtain h | h | h := lt_trichotomy a b
      · exact absurd hab (ne_of_lt (hstrict (Set.mem_univ _) (Set.mem_univ _) h))
      · exact h
      · exact absurd hab (ne_of_gt (hstrict (Set.mem_univ _) (Set.mem_univ _) h))
    have hFinj : Function.Injective (γ ∘ φ) := by
      intro a b hab
      have haD : φ a ∈ D := hφrange ▸ Set.mem_range_self a
      have hbD : φ b ∈ D := hφrange ▸ Set.mem_range_self b
      exact hφinj (hInj haD hbD hab)
    have hFsurj : Function.Surjective (γ ∘ φ) := by
      intro y
      have hy : y ∈ γ '' D := himg.symm ▸ Set.mem_univ y
      obtain ⟨t, htD, rfl⟩ := hy
      obtain ⟨s, rfl⟩ := hφrange.symm ▸ htD
      exact ⟨s, rfl⟩
    exact Or.inr ⟨(hFld.diffeomorphOfBijective ⟨hFinj, hFsurj⟩).symm.trans
      omLinEquiv.toDiffeomorph⟩
  · -- Non-injective case: the maximal curve is periodic, so `M ≃ Circle`.
    have hpair : ∃ t₁ t₂ : ℝ, t₁ ∈ D ∧ t₂ ∈ D ∧ t₁ < t₂ ∧ γ t₁ = γ t₂ := by
      by_contra hcon
      have hInj' : Set.InjOn γ D := by
        intro a haD b hbD hab
        obtain h | h | h := lt_trichotomy a b
        · exact (hcon ⟨a, b, haD, hbD, h, hab⟩).elim
        · exact h
        · exact (hcon ⟨b, a, hbD, haD, h, hab.symm⟩).elim
      exact hInj hInj'
    obtain ⟨t₁, t₂, ht₁, ht₂, hlt, heq⟩ := hpair
    obtain ⟨hDuniv, hper⟩ :=
      om_maximal_unitSpeed_periodic_of_eq g α₀ D γ hDadm hmax t₁ t₂ ht₁ ht₂
        hlt heq
    have hTne : t₂ - t₁ ≠ 0 := ne_of_gt (by linarith)
    obtain ⟨δ, hδpos, hδinj⟩ :=
      om_exists_injOn_of_unitSpeed g D γ hDopen hγunit 0 h0D
    have hδinj' : Set.InjOn γ (Set.Ioo (-δ) δ) := by
      have e : Set.Ioo ((0 : ℝ) - δ) (0 + δ) = Set.Ioo (-δ) δ := by
        rw [zero_sub, zero_add]
      rwa [e] at hδinj
    have hcoin : ∀ s t : ℝ, s ≠ t → γ s = γ t → ∀ u, γ (u + (t - s)) = γ u := by
      intro s t hst heq' u
      obtain h | h := lt_or_gt_of_ne hst
      · have hsD : s ∈ D := by
        rw [hDuniv]
        exact Set.mem_univ s
        have htD : t ∈ D := by
          rw [hDuniv]
          exact Set.mem_univ t
        exact (om_maximal_unitSpeed_periodic_of_eq g α₀ D γ hDadm hmax s t
          hsD htD h heq').2 u
      · have hsD : s ∈ D := by
        rw [hDuniv]
        exact Set.mem_univ s
        have htD : t ∈ D := by
          rw [hDuniv]
          exact Set.mem_univ t
        have h2 := (om_maximal_unitSpeed_periodic_of_eq g α₀ D γ hDadm hmax t s
          htD hsD h heq'.symm).2
        have e2 := h2 (u + (t - s))
        have e3 : u + (t - s) + (s - t) = u := by ring
        rwa [e3] at e2
    obtain ⟨T₀, hT₀pos, _, hiff⟩ :=
      om_exists_minimal_period γ δ hδpos hδinj' (t₂ - t₁) hTne hper hcoin
    have hsurj : Function.Surjective γ := by
      intro y
      have hy : y ∈ γ '' D := himg.symm ▸ Set.mem_univ y
      obtain ⟨t, _, ht⟩ := hy
      exact ⟨t, ht⟩
    have hld : ∀ t : ℝ, IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ t := by
      intro t
      have htD : t ∈ D := by
        rw [hDuniv]
        exact Set.mem_univ t
      exact om_isLocalDiffeomorphAt_of_unitSpeed g D γ hDopen hγunit t htD
    obtain ⟨hC⟩ := om_nonempty_diffeomorph_circle_of_periodic γ hsurj hld T₀
      hT₀pos hiff
    exact Or.inl ⟨hC.symm⟩

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_blackbox_interior](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_blackbox_interior (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M] :
  Nonempty (↥(ombInterior M) ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) ∨
    Nonempty (↥(ombInterior M) ≃ₘ⟮𝓡 1, 𝓡 1⟯ (EuclideanSpace ℝ (Fin 1))) :=
  connected_boundaryless_one_manifold_classification ↥(ombInterior M)

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_valPsi_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_valPsi_injective (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
  (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M)) :
  Function.Injective (ombValPsi M Ψ) := by
  have h : Function.Injective (Subtype.val ∘ ⇑Ψ) :=
    Subtype.val_injective.comp Ψ.toEquiv.injective
  have e : (Subtype.val ∘ ⇑Ψ) = ombValPsi M Ψ := rfl
  rwa [e] at h

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_mem_interior_eq_valPsi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_mem_interior_eq_valPsi (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
  (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M)) (m : M)
  (hm : m ∈ (ombInterior M : Set M)) :
  ∃ u₀, ombValPsi M Ψ u₀ = m := by
  refine ⟨Ψ.symm ⟨m, hm⟩, ?_⟩
  change ((Ψ (Ψ.symm ⟨m, hm⟩) : ↥(ombInterior M)) : M) = m
  rw [Ψ.apply_symm_apply]

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_eventually_nhdsGT_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_eventually_nhdsGT_Ioo {P : ℝ → Prop}
  (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), P t) : ∃ δ > 0, ∀ t ∈ Set.Ioo 0 δ, P t := by
  rw [eventually_nhdsWithin_iff] at h
  rw [Metric.eventually_nhds_iff_ball] at h
  obtain ⟨δ, hδpos, hδ⟩ := h
  refine ⟨δ, hδpos, ?_⟩
  intro t ht
  rw [Set.mem_Ioo] at ht
  refine hδ t ?_ ht.1
  rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [hδpos, ht.1, ht.2]

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_end_not_both](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_end_not_both (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
  (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
  (x₀ : ↥(ombInterior M)) (p : M)
  (hBot : Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atBot)
  (hTop : Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atTop) :
  False :=
  hBot.not_tendsto Filter.disjoint_atBot_atTop hTop

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_valPsi_openEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_valPsi_openEmbedding (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
  (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M)) :
  Topology.IsOpenEmbedding (ombValPsi M Ψ) := by
  have hS : IsOpen (ombInterior M : Set M) := (ombInterior M).2
  have e : ombValPsi M Ψ = Subtype.val ∘ ⇑Ψ := rfl
  rw [e]
  exact hS.isOpenEmbedding_subtypeVal.comp Ψ.toHomeomorph.isOpenEmbedding

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_mapClusterPt_atBot_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_mapClusterPt_atBot_not_mem (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
  (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
  (m : M) (hm : MapClusterPt m Filter.atBot (ombValPsi M Ψ))
  (hmS : m ∈ (ombInterior M : Set M)) : False := by
  obtain ⟨u₀, hu₀⟩ := omb_mem_interior_eq_valPsi M Ψ m hmS
  have hopen : IsOpen ((ombValPsi M Ψ) '' Set.Ioo (u₀ - 1) (u₀ + 1)) :=
    (omb_valPsi_openEmbedding M Ψ).isOpenMap _ isOpen_Ioo
  have hmem : m ∈ (ombValPsi M Ψ) '' Set.Ioo (u₀ - 1) (u₀ + 1) := by
    rw [← hu₀]
    exact ⟨u₀, ⟨by linarith, by linarith⟩, rfl⟩
  have hfreq : ∃ᶠ u in Filter.atBot,
    ombValPsi M Ψ u ∈ (ombValPsi M Ψ) '' Set.Ioo (u₀ - 1) (u₀ + 1) :=
    mapClusterPt_iff_frequently.mp hm _ (hopen.mem_nhds hmem)
  have hev : ∀ᶠ u in Filter.atBot, u < u₀ - 1 :=
    Filter.eventually_lt_atBot (u₀ - 1)
  obtain ⟨u, huN, huLt⟩ := (hfreq.and_eventually hev).exists
  obtain ⟨v, hvIoo, hvu⟩ := huN
  have hvu' : v = u := omb_valPsi_injective M Ψ hvu
  rw [hvu'] at hvIoo
  linarith [hvIoo.1, huLt]

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_mapClusterPt_atTop_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_mapClusterPt_atTop_not_mem (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
  (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
  (m : M) (hm : MapClusterPt m Filter.atTop (ombValPsi M Ψ))
  (hmS : m ∈ (ombInterior M : Set M)) : False := by
  obtain ⟨u₀, hu₀⟩ := omb_mem_interior_eq_valPsi M Ψ m hmS
  have hopen : IsOpen ((ombValPsi M Ψ) '' Set.Ioo (u₀ - 1) (u₀ + 1)) :=
    (omb_valPsi_openEmbedding M Ψ).isOpenMap _ isOpen_Ioo
  have hmem : m ∈ (ombValPsi M Ψ) '' Set.Ioo (u₀ - 1) (u₀ + 1) := by
    rw [← hu₀]
    exact ⟨u₀, ⟨by linarith, by linarith⟩, rfl⟩
  have hfreq : ∃ᶠ u in Filter.atTop,
    ombValPsi M Ψ u ∈ (ombValPsi M Ψ) '' Set.Ioo (u₀ - 1) (u₀ + 1) :=
    mapClusterPt_iff_frequently.mp hm _ (hopen.mem_nhds hmem)
  have hev : ∀ᶠ u in Filter.atTop, u₀ + 1 < u :=
    Filter.eventually_gt_atTop (u₀ + 1)
  obtain ⟨u, huN, huGt⟩ := (hfreq.and_eventually hev).exists
  obtain ⟨v, hvIoo, hvu⟩ := huN
  have hvu' : v = u := omb_valPsi_injective M Ψ hvu
  rw [hvu'] at hvIoo
  linarith [hvIoo.2, huGt]

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[ombBlend_eq_theta_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma ombBlend_eq_theta_of_le (θ : ℝ → ℝ) (α β a : ℝ) (ha : 0 < a)
  (t : ℝ) (ht : t ≤ a) : ombBlend θ α β a t = θ t := by
  have hs : (t - a) / a ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt ha)
  simp only [ombBlend, Real.smoothTransition.zero_of_nonpos hs]
  ring

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[ombBlend_eq_line_of_ge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma ombBlend_eq_line_of_ge (θ : ℝ → ℝ) (α β a : ℝ) (ha : 0 < a)
  (t : ℝ) (ht : 2 * a ≤ t) : ombBlend θ α β a t = α + β * t := by
  have hs : 1 ≤ (t - a) / a := by
    rw [le_div_iff₀ ha]
    linarith
  simp only [ombBlend, Real.smoothTransition.one_of_one_le hs]
  ring

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[ombBlend_contDiffOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma ombBlend_contDiffOn (θ : ℝ → ℝ) (α β a b : ℝ) (ha : 0 < a)
  (hab : 2 * a < b) (hθ : ContDiffOn ℝ ∞ θ (Set.Ioo 0 b)) :
  ContDiffOn ℝ ∞ (ombBlend θ α β a) (Set.Ioi 0) := by
  have hℓC : ContDiff ℝ ∞ (fun s : ℝ => α + β * s) := by fun_prop
  have hsC : ContDiff ℝ ∞ (fun s : ℝ => (s - a) / a) := by fun_prop
  intro t ht
  rw [Set.mem_Ioi] at ht
  obtain htb | htb := lt_or_ge t b
  · have htIoo : t ∈ Set.Ioo (0 : ℝ) b := ⟨ht, htb⟩
    have hLam : ContDiffAt ℝ ∞
      (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t :=
      Real.smoothTransition.contDiffAt.comp t (hsC.contDiffAt)
    have hθt : ContDiffAt ℝ ∞ θ t := hθ.contDiffAt (isOpen_Ioo.mem_nhds htIoo)
    have hℓt : ContDiffAt ℝ ∞ (fun s : ℝ => α + β * s) t := hℓC.contDiffAt
    have hcombo : ContDiffAt ℝ ∞ (fun s : ℝ =>
      (1 - Real.smoothTransition ((s - a) / a)) * θ s +
      Real.smoothTransition ((s - a) / a) * (α + β * s)) t :=
      ((contDiffAt_const.sub hLam).mul hθt).add (hLam.mul hℓt)
    exact hcombo.contDiffWithinAt
  · have h2a : 2 * a < t := lt_of_lt_of_le hab htb
    have hev : ombBlend θ α β a =ᶠ[𝓝 t] (fun s : ℝ => α + β * s) := by
      filter_upwards [Ioi_mem_nhds h2a] with s hs
      exact ombBlend_eq_line_of_ge θ α β a ha s (le_of_lt hs)
    exact (hℓC.contDiffAt.congr_of_eventuallyEq hev).contDiffWithinAt

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[ombBlend_lam_deriv_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma ombBlend_lam_deriv_nonneg (a t : ℝ) (ha : 0 < a) :
  0 ≤ deriv (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t := by
  have hS : HasDerivAt Real.smoothTransition
    (deriv Real.smoothTransition ((t - a) / a)) ((t - a) / a) :=
    Real.smoothTransition.contDiffAt.differentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0) |>.hasDerivAt
  have hs : HasDerivAt (fun s : ℝ => (s - a) / a) (1 / a) t := by
    have h := ((HasDerivAt.sub (hasDerivAt_id t) (hasDerivAt_const t a)).div_const a)
    simpa using h
  have hcomp := hS.comp t hs
  have ed : deriv (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t =
    deriv Real.smoothTransition ((t - a) / a) * (1 / a) := hcomp.deriv
  rw [ed]
  exact mul_nonneg (Monotone.deriv_nonneg Real.smoothTransition.monotone)
    (le_of_lt (one_div_pos.mpr ha))

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[ombBlend_lam_deriv_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma ombBlend_lam_deriv_zero_of_lt (a t : ℝ) (ha : 0 < a)
  (ht : t < a) :
  deriv (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t = 0 := by
  have hev : (fun s : ℝ => Real.smoothTransition ((s - a) / a)) =ᶠ[𝓝 t]
    (fun _ => 0) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    have hle : (s - a) / a ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [Set.mem_Iio.mp hs])
        (le_of_lt ha)
    exact Real.smoothTransition.zero_of_nonpos hle
  rw [hev.deriv_eq]
  exact deriv_const _ _

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[ombBlend_lam_deriv_zero_of_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma ombBlend_lam_deriv_zero_of_gt (a t : ℝ) (ha : 0 < a)
  (ht : 2 * a < t) :
  deriv (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t = 0 := by
  have hev : (fun s : ℝ => Real.smoothTransition ((s - a) / a)) =ᶠ[𝓝 t]
    (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hge : 1 ≤ (s - a) / a := by
      rw [le_div_iff₀ ha]
      linarith [Set.mem_Ioi.mp hs]
    exact Real.smoothTransition.one_of_one_le hge
  rw [hev.deriv_eq]
  exact deriv_const _ _

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[ombBlend_affine_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma ombBlend_affine_deriv (α β t : ℝ) :
  deriv (fun s : ℝ => α + β * s) t = β := by
  simp

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[ombBlend_deriv_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma ombBlend_deriv_pos (θ : ℝ → ℝ) (α β a b : ℝ) (ha : 0 < a)
  (hab : 2 * a < b) (hθ : ContDiffOn ℝ ∞ θ (Set.Ioo 0 b))
  (hpos : ∀ t ∈ Set.Ioo 0 b, 0 < deriv θ t) (hβ : 0 < β)
  (hle : θ (2 * a) ≤ α + β * a) (t : ℝ) (ht : 0 < t) :
  0 < deriv (ombBlend θ α β a) t := by
  by_cases htb : t < b
  · have htIoo : t ∈ Set.Ioo (0 : ℝ) b := ⟨ht, htb⟩
    have hθt : ContDiffAt ℝ ∞ θ t := hθ.contDiffAt (isOpen_Ioo.mem_nhds htIoo)
    have hθd : HasDerivAt θ (deriv θ t) t :=
      (hθt.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasDerivAt
    have hsC : ContDiff ℝ ∞ (fun s : ℝ => (s - a) / a) := by fun_prop
    have hlamC : ContDiffAt ℝ ∞
      (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t :=
      Real.smoothTransition.contDiffAt.comp t (hsC.contDiffAt)
    have hlamd : HasDerivAt (fun s : ℝ => Real.smoothTransition ((s - a) / a))
      (deriv (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t) t :=
      (hlamC.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasDerivAt
    have hℓC : ContDiff ℝ ∞ (fun s : ℝ => α + β * s) := by fun_prop
    have hld : HasDerivAt (fun s : ℝ => α + β * s)
      (deriv (fun s : ℝ => α + β * s) t) t :=
      ((hℓC.differentiable (by simp : (∞ : ℕ∞ω) ≠ 0)).differentiableAt).hasDerivAt
    rw [ombBlend_affine_deriv α β t] at hld
    set S := Real.smoothTransition ((t - a) / a) with hSdef
    set S' := deriv (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t
      with hS'def
    have h1 : HasDerivAt (fun s : ℝ => 1 - Real.smoothTransition ((s - a) / a))
      (0 - S') t :=
      HasDerivAt.sub (hasDerivAt_const t 1) hlamd
    have h2 : HasDerivAt
      (fun s : ℝ => (1 - Real.smoothTransition ((s - a) / a)) * θ s)
      ((0 - S') * θ t + (1 - S) * deriv θ t) t :=
      HasDerivAt.mul h1 hθd
    have h3 : HasDerivAt
      (fun s : ℝ => Real.smoothTransition ((s - a) / a) * (α + β * s))
      (S' * (α + β * t) + S * β) t :=
      HasDerivAt.mul hlamd hld
    have hψ : HasDerivAt (ombBlend θ α β a)
      (((0 - S') * θ t + (1 - S) * deriv θ t) +
        (S' * (α + β * t) + S * β)) t :=
      HasDerivAt.add h2 h3
    have eψ : deriv (ombBlend θ α β a) t =
      (((0 - S') * θ t + (1 - S) * deriv θ t) +
        (S' * (α + β * t) + S * β)) := hψ.deriv
    have hSnn : 0 ≤ S := Real.smoothTransition.nonneg _
    have hS1 : S ≤ 1 := Real.smoothTransition.le_one _
    have hθ' : 0 < deriv θ t := hpos t htIoo
    have hm : 0 < min (deriv θ t) β := lt_min hθ' hβ
    have c1 : (1 - S) * min (deriv θ t) β ≤ (1 - S) * deriv θ t :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
    have c2 : S * min (deriv θ t) β ≤ S * β :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hSnn
    have hring : (1 - S) * min (deriv θ t) β + S * min (deriv θ t) β =
      min (deriv θ t) β := by ring
    have hlast : 0 ≤ S' * ((α + β * t) - θ t) := by
      obtain hta | hta := lt_or_ge t a
      · have e0 : S' = 0 := ombBlend_lam_deriv_zero_of_lt a t ha hta
        simp [e0]
      · rcases le_or_gt t (2 * a) with ht2 | ht2
        · have hgap : θ t ≤ α + β * t := by
          have hmonoθ : StrictMonoOn θ (Set.Ioo 0 b) :=
            strictMonoOn_of_deriv_pos (convex_Ioo 0 b) hθ.continuousOn
              (by rw [interior_Ioo]; exact hpos)
          have h2aIoo : 2 * a ∈ Set.Ioo (0 : ℝ) b := ⟨by linarith, hab⟩
          have hθle : θ t ≤ θ (2 * a) :=
            hmonoθ.monotoneOn htIoo h2aIoo ht2
          have hline : α + β * a ≤ α + β * t := by
            have hmul : β * a ≤ β * t :=
              mul_le_mul_of_nonneg_left hta (le_of_lt hβ)
            linarith
          exact le_trans hθle (le_trans hle hline)
          exact mul_nonneg (ombBlend_lam_deriv_nonneg a t ha)
            (sub_nonneg.mpr hgap)
        · have e0 : S' = 0 := ombBlend_lam_deriv_zero_of_gt a t ha ht2
          simp [e0]
    have hring2 : (((0 - S') * θ t + (1 - S) * deriv θ t) +
      (S' * (α + β * t) + S * β)) =
      ((1 - S) * deriv θ t + S * β) + S' * ((α + β * t) - θ t) := by ring
    rw [eψ, hring2]
    linarith
  · have htle : b ≤ t := le_of_not_gt htb
    have h2a : 2 * a < t := lt_of_lt_of_le hab htle
    have hev : ombBlend θ α β a =ᶠ[𝓝 t] (fun s : ℝ => α + β * s) := by
      filter_upwards [Ioi_mem_nhds h2a] with s hs
      exact ombBlend_eq_line_of_ge θ α β a ha s (le_of_lt hs)
    rwa [hev.deriv_eq, ombBlend_affine_deriv]

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_exists_blend_line](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_exists_blend_line (θ : ℝ → ℝ) (α β a b : ℝ) (ha : 0 < a)
  (hab : 2 * a < b) (hθ : ContDiffOn ℝ ∞ θ (Set.Ioo 0 b))
  (hpos : ∀ t ∈ Set.Ioo 0 b, 0 < deriv θ t) (hβ : 0 < β)
  (hle : θ (2 * a) ≤ α + β * a) :
  ∃ ψ : ℝ → ℝ, ContDiffOn ℝ ∞ ψ (Set.Ioi 0) ∧
    (∀ t > 0, 0 < deriv ψ t) ∧
    Set.EqOn ψ θ (Set.Ioc 0 a) ∧
    (∀ t ≥ 2 * a, ψ t = α + β * t) := by
  refine ⟨ombBlend θ α β a, ombBlend_contDiffOn θ α β a b ha hab hθ, ?_, ?_, ?_⟩
  · intro t ht
    exact ombBlend_deriv_pos θ α β a b ha hab hθ hpos hβ hle t ht
  · intro t ht
    rw [Set.mem_Ioc] at ht
    exact ombBlend_eq_theta_of_le θ α β a ha t ht.2
  · intro t ht
    exact ombBlend_eq_line_of_ge θ α β a ha t ht

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_interp_setup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_interp_setup (θ₁ θ₂ : ℝ → ℝ) (b : ℝ) (hb0 : 0 < b)
  (hb12 : b ≤ 1 / 2)
  (hθ₁ : ContDiffOn ℝ ∞ θ₁ (Set.Ioo 0 b))
  (hθ₂ : ContDiffOn ℝ ∞ θ₂ (Set.Ioo 0 b))
  (hpos₁ : ∀ t ∈ Set.Ioo 0 b, 0 < deriv θ₁ t)
  (hneg₂ : ∀ t ∈ Set.Ioo 0 b, deriv θ₂ t < 0)
  (hlim₁ : Filter.Tendsto θ₁ (𝓝[>] 0) Filter.atBot)
  (hlim₂ : Filter.Tendsto θ₂ (𝓝[>] 0) Filter.atTop) :
  ∃ a β : ℝ, ∃ ψ₁ ψ₂ : ℝ → ℝ, 0 < a ∧ a < b ∧ a < 1 / 4 ∧ 0 < β ∧
    ContDiffOn ℝ ∞ ψ₁ (Set.Ioi 0) ∧ ContDiffOn ℝ ∞ ψ₂ (Set.Ioi 0) ∧
    (∀ t > 0, 0 < deriv ψ₁ t) ∧ (∀ t > 0, 0 < deriv ψ₂ t) ∧
    Set.EqOn ψ₁ θ₁ (Set.Ioo 0 a) ∧ Set.EqOn ψ₂ (-θ₂) (Set.Ioo 0 a) ∧
    (∀ t ≥ 2 * a, ψ₁ t = (θ₁ (2 * a) - β * a) + β * t) ∧
    (∀ s ≥ 2 * a, ψ₂ s = (-θ₁ (2 * a) - β * (1 - a)) + β * s) := by
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), θ₁ t < 0 :=
    hlim₁.eventually (Filter.eventually_lt_atBot 0)
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < θ₂ t :=
    hlim₂.eventually (Filter.eventually_gt_atTop 0)
  obtain ⟨δ, hδpos, hδ⟩ := omb_eventually_nhdsGT_Ioo (hev1.and hev2)
  set a := min δ b / 4 with hadef
  have hminpos : 0 < min δ b := lt_min hδpos hb0
  have ha : 0 < a := by linarith
  have hminδ : min δ b ≤ δ := min_le_left _ _
  have hminb : min δ b ≤ b := min_le_right _ _
  have hab : a < b := by linarith
  have ha14 : a < 1 / 4 := by linarith
  have h2aδ : 2 * a < δ := by linarith
  have h2ab : 2 * a < b := by linarith
  have h2amem : 2 * a ∈ Set.Ioo (0 : ℝ) δ := ⟨by linarith, h2aδ⟩
  have hθ₁2 : θ₁ (2 * a) < 0 := (hδ (2 * a) h2amem).1
  have hθ₂2 : 0 < θ₂ (2 * a) := (hδ (2 * a) h2amem).2
  set β := (θ₂ (2 * a) - θ₁ (2 * a)) / (1 - 2 * a) with hβdef
  have hβpos : 0 < 1 - 2 * a := by linarith
  have hβ : 0 < β := div_pos (by linarith) hβpos
  have hβcancel : β * (1 - 2 * a) = θ₂ (2 * a) - θ₁ (2 * a) :=
    div_mul_cancel₀ _ (by linarith)
  have hle₁ : θ₁ (2 * a) ≤ (θ₁ (2 * a) - β * a) + β * a := by linarith
  have hring₂ : -β * (1 - a) + β * a = -(β * (1 - 2 * a)) := by ring
  have hle₂ : (-θ₂) (2 * a) ≤ (-θ₁ (2 * a) - β * (1 - a)) + β * a := by
    have hpi : (-θ₂) (2 * a) = -θ₂ (2 * a) := rfl
    rw [hpi]
    linarith [hβcancel, hring₂]
  have hnegθ₂ : ContDiffOn ℝ ∞ (-θ₂) (Set.Ioo 0 b) := hθ₂.neg
  have hnegpos : ∀ t ∈ Set.Ioo 0 b, 0 < deriv (-θ₂) t := by
    intro t ht
    rw [deriv.neg]
    linarith [hneg₂ t ht]
  obtain ⟨ψ₁, hψ₁D, hψ₁pos, hψ₁eq, hψ₁line⟩ :=
    omb_exists_blend_line θ₁ (θ₁ (2 * a) - β * a) β a b ha h2ab hθ₁ hpos₁
      hβ hle₁
  obtain ⟨ψ₂, hψ₂D, hψ₂pos, hψ₂eq, hψ₂line⟩ :=
    omb_exists_blend_line (-θ₂) (-θ₁ (2 * a) - β * (1 - a)) β a b ha h2ab
      hnegθ₂ hnegpos hβ hle₂
  refine ⟨a, β, ψ₁, ψ₂, ha, hab, ha14, hβ, hψ₁D, hψ₂D, hψ₁pos, hψ₂pos, ?_, ?_,
    hψ₁line, hψ₂line⟩
  · intro s hs
    exact hψ₁eq (Set.Ioo_subset_Ioc_self hs)
  · intro s hs
    exact hψ₂eq (Set.Ioo_subset_Ioc_self hs)

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_exists_interpolation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_exists_interpolation (θ₁ θ₂ : ℝ → ℝ) (b : ℝ) (hb0 : 0 < b)
  (hb12 : b ≤ 1 / 2)
  (hθ₁ : ContDiffOn ℝ ∞ θ₁ (Set.Ioo 0 b))
  (hθ₂ : ContDiffOn ℝ ∞ θ₂ (Set.Ioo 0 b))
  (hpos₁ : ∀ t ∈ Set.Ioo 0 b, 0 < deriv θ₁ t)
  (hneg₂ : ∀ t ∈ Set.Ioo 0 b, deriv θ₂ t < 0)
  (hlim₁ : Filter.Tendsto θ₁ (𝓝[>] 0) Filter.atBot)
  (hlim₂ : Filter.Tendsto θ₂ (𝓝[>] 0) Filter.atTop) :
  ∃ a : ℝ, 0 < a ∧ a < b ∧ ∃ φ : ℝ → ℝ,
    ContDiffOn ℝ ∞ φ (Set.Ioo 0 1) ∧
    (∀ t ∈ Set.Ioo 0 1, 0 < deriv φ t) ∧
    φ '' Set.Ioo 0 1 = Set.univ ∧
    Set.EqOn φ θ₁ (Set.Ioo 0 a) ∧
    Set.EqOn φ (fun t => θ₂ (1 - t)) (Set.Ioo (1 - a) 1) := by
  obtain ⟨a, β, ψ₁, ψ₂, ha, hab, ha14, hβ, hψ₁D, hψ₂D, hψ₁pos, hψ₂pos,
    eψ₁θ, eψ₂θ, hψ₁line, hψ₂line⟩ :=
    omb_interp_setup θ₁ θ₂ b hb0 hb12 hθ₁ hθ₂ hpos₁ hneg₂ hlim₁ hlim₂
  have h2a1 : 2 * a < 1 - 2 * a := by linarith
  have hhalf1 : 2 * a < 1 / 2 := by linarith
  have hhalf2 : (1 : ℝ) / 2 < 1 - 2 * a := by linarith
  have hagree : ∀ t ∈ Set.Icc (2 * a) (1 - 2 * a), -ψ₂ (1 - t) = ψ₁ t := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have h1t : 2 * a ≤ 1 - t := by linarith [ht.2]
    rw [hψ₁line t ht.1, hψ₂line (1 - t) h1t]
    ring
  set φ : ℝ → ℝ := fun t => if t ≤ 1 / 2 then ψ₁ t else -ψ₂ (1 - t)
    with hφdef
  have eleft : ∀ s ∈ Set.Ioo (0 : ℝ) a, φ s = θ₁ s := by
    intro s hs
    have hs' : s < a := (Set.mem_Ioo.mp hs).2
    have hle : s ≤ 1 / 2 := by linarith [hs', ha14]
    change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = θ₁ s
    rw [ite_eq_left hle]
    exact eψ₁θ hs
  have eright : ∀ s ∈ Set.Ioo (1 - a) 1, φ s = θ₂ (1 - s) := by
    intro s hs
    have hs' := Set.mem_Ioo.mp hs
    have hle : ¬ s ≤ 1 / 2 := by linarith [hs'.1, ha14]
    change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = θ₂ (1 - s)
    rw [ite_eq_right hle]
    have h1s : (1 - s) ∈ Set.Ioo (0 : ℝ) a :=
      ⟨by linarith [hs'.2], by linarith [hs'.1]⟩
    have h2 := eψ₂θ h1s
    simpa using congrArg (fun x => -x) h2
  have hφD : ContDiffOn ℝ ∞ φ (Set.Ioo 0 1) := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    obtain h1 | h1 := lt_or_ge t (1 - 2 * a)
    · have htmem : t ∈ Set.Ioo (0 : ℝ) (1 - 2 * a) := ⟨ht.1, h1⟩
      have hev : φ =ᶠ[𝓝 t] ψ₁ := by
        filter_upwards [isOpen_Ioo.mem_nhds htmem] with s hs
        rw [Set.mem_Ioo] at hs
        by_cases hle : s ≤ 1 / 2
        · change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = ψ₁ s
          rw [ite_eq_left hle]
        · have hs2a : 2 * a < s := by linarith
          have hsIcc : s ∈ Set.Icc (2 * a) (1 - 2 * a) := by
            rw [Set.mem_Icc]
            exact ⟨le_of_lt hs2a, le_of_lt hs.2⟩
          change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = ψ₁ s
          rw [ite_eq_right hle]
          exact hagree s hsIcc
      have hψ₁at : ContDiffAt ℝ ∞ ψ₁ t :=
        hψ₁D.contDiffAt (isOpen_Ioi.mem_nhds ht.1)
      exact (hψ₁at.congr_of_eventuallyEq hev).contDiffWithinAt
    · have ht2a : 2 * a < t := lt_of_lt_of_le h2a1 h1
      have htmem : t ∈ Set.Ioo (2 * a) 1 := ⟨ht2a, ht.2⟩
      have hev : φ =ᶠ[𝓝 t] (fun s => -ψ₂ (1 - s)) := by
        filter_upwards [isOpen_Ioo.mem_nhds htmem] with s hs
        rw [Set.mem_Ioo] at hs
        by_cases hle : s ≤ 1 / 2
        · have hsIcc : s ∈ Set.Icc (2 * a) (1 - 2 * a) := by
          rw [Set.mem_Icc]
          refine ⟨le_of_lt hs.1, ?_⟩
          linarith [hle, hhalf2]
          change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = -ψ₂ (1 - s)
          rw [ite_eq_left hle]
          exact (hagree s hsIcc).symm
        · change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = -ψ₂ (1 - s)
          rw [ite_eq_right hle]
      have h1t : (0 : ℝ) < 1 - t := by linarith [ht.2]
      have hψ₂at : ContDiffAt ℝ ∞ ψ₂ (1 - t) :=
        hψ₂D.contDiffAt (isOpen_Ioi.mem_nhds h1t)
      have hsub : ContDiffAt ℝ ∞ (fun s : ℝ => 1 - s) t :=
        contDiffAt_const.sub contDiffAt_id
      have hcomp : ContDiffAt ℝ ∞ (fun s => -ψ₂ (1 - s)) t :=
        (hψ₂at.comp t hsub).neg
      exact (hcomp.congr_of_eventuallyEq hev).contDiffWithinAt
  have hφderiv : ∀ t ∈ Set.Ioo 0 1, 0 < deriv φ t := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    obtain h1 | h1 := lt_or_ge t (1 - 2 * a)
    · have htmem : t ∈ Set.Ioo (0 : ℝ) (1 - 2 * a) := ⟨ht.1, h1⟩
      have hev : φ =ᶠ[𝓝 t] ψ₁ := by
        filter_upwards [isOpen_Ioo.mem_nhds htmem] with s hs
        rw [Set.mem_Ioo] at hs
        by_cases hle : s ≤ 1 / 2
        · change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = ψ₁ s
          rw [ite_eq_left hle]
        · have hs2a : 2 * a < s := by linarith
          have hsIcc : s ∈ Set.Icc (2 * a) (1 - 2 * a) := by
            rw [Set.mem_Icc]
            exact ⟨le_of_lt hs2a, le_of_lt hs.2⟩
          change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = ψ₁ s
          rw [ite_eq_right hle]
          exact hagree s hsIcc
      rw [hev.deriv_eq]
      exact hψ₁pos t ht.1
    · have ht2a : 2 * a < t := lt_of_lt_of_le h2a1 h1
      have htmem : t ∈ Set.Ioo (2 * a) 1 := ⟨ht2a, ht.2⟩
      have hev : φ =ᶠ[𝓝 t] (fun s => -ψ₂ (1 - s)) := by
        filter_upwards [isOpen_Ioo.mem_nhds htmem] with s hs
        rw [Set.mem_Ioo] at hs
        by_cases hle : s ≤ 1 / 2
        · have hsIcc : s ∈ Set.Icc (2 * a) (1 - 2 * a) := by
          rw [Set.mem_Icc]
          refine ⟨le_of_lt hs.1, ?_⟩
          linarith [hle, hhalf2]
          change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = -ψ₂ (1 - s)
          rw [ite_eq_left hle]
          exact (hagree s hsIcc).symm
        · change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = -ψ₂ (1 - s)
          rw [ite_eq_right hle]
      rw [hev.deriv_eq]
      have h1t : (0 : ℝ) < 1 - t := by linarith [ht.2]
      have hψ₂d : HasDerivAt ψ₂ (deriv ψ₂ (1 - t)) (1 - t) :=
        ((hψ₂D.contDiffAt (isOpen_Ioi.mem_nhds h1t)).differentiableAt
          (by simp : (∞ : ℕ∞ω) ≠ 0)).hasDerivAt
      have hsubd : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
        have h := HasDerivAt.sub (hasDerivAt_const t 1) (hasDerivAt_id t)
        have efun : ((fun _ : ℝ => 1) - id) = (fun s : ℝ => 1 - s) := by
          funext s
          rfl
        have eval : (0 : ℝ) - 1 = -1 := by ring
        rwa [efun, eval] at h
      have hcompd := HasDerivAt.comp t hψ₂d hsubd
      have hnegd := HasDerivAt.neg hcompd
      have e2 : deriv (fun s : ℝ => -ψ₂ (1 - s)) t = deriv ψ₂ (1 - t) := by
        have e := hnegd.deriv
        have efun : (-(ψ₂ ∘ (fun s : ℝ => 1 - s))) =
          (fun s : ℝ => -ψ₂ (1 - s)) := by
          funext s
          rfl
        have eval : -(deriv ψ₂ (1 - t) * -1) = deriv ψ₂ (1 - t) := by ring
        rwa [efun, eval] at e
      rw [e2]
      exact hψ₂pos (1 - t) h1t
  have hφsurj : φ '' Set.Ioo 0 1 = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    have hevLt : ∀ᶠ s in 𝓝[>] (0 : ℝ), θ₁ s < y :=
      hlim₁.eventually (Filter.eventually_lt_atBot y)
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := omb_eventually_nhdsGT_Ioo hevLt
    set s₁ := min δ₁ a / 2 with hs₁def
    have hm₁ : (0 : ℝ) < min δ₁ a := lt_min hδ₁pos ha
    have hs₁a : s₁ ∈ Set.Ioo (0 : ℝ) a :=
      ⟨by linarith [hs₁def, hm₁], by linarith [hs₁def, min_le_right δ₁ a]⟩
    have hs₁δ : s₁ ∈ Set.Ioo (0 : ℝ) δ₁ :=
      ⟨by linarith [hs₁def, hm₁], by linarith [hs₁def, min_le_left δ₁ a]⟩
    have hφs₁ : φ s₁ < y := by
      rw [eleft s₁ hs₁a]
      exact hδ₁ s₁ hs₁δ
    have hevGt : ∀ᶠ s in 𝓝[>] (0 : ℝ), y < θ₂ s :=
      hlim₂.eventually (Filter.eventually_gt_atTop y)
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := omb_eventually_nhdsGT_Ioo hevGt
    set s₂' := min δ₂ a / 2 with hs₂def
    have hm₂ : (0 : ℝ) < min δ₂ a := lt_min hδ₂pos ha
    have hs₂'a : s₂' ∈ Set.Ioo (0 : ℝ) a :=
      ⟨by linarith [hs₂def, hm₂], by linarith [hs₂def, min_le_right δ₂ a]⟩
    have hs₂'δ : s₂' ∈ Set.Ioo (0 : ℝ) δ₂ :=
      ⟨by linarith [hs₂def, hm₂], by linarith [hs₂def, min_le_left δ₂ a]⟩
    set s₂ := 1 - s₂' with hs₂def
    have hs₂ : s₂ ∈ Set.Ioo (1 - a) 1 :=
      ⟨by linarith [hs₂'a.2], by linarith [hs₂'a.1]⟩
    have hφs₂ : y < φ s₂ := by
      have e : φ s₂ = θ₂ (1 - s₂) := eright s₂ hs₂
      have e1s : (1 : ℝ) - s₂ = s₂' := by linarith
      rw [e, e1s]
      exact hδ₂ s₂' hs₂'δ
    have hs₁₂ : s₁ < s₂ := by linarith [hs₁a.2, hs₂.1, ha14]
    have hmem : y ∈ Set.Icc (φ s₁) (φ s₂) := ⟨le_of_lt hφs₁, le_of_lt hφs₂⟩
    have hcont : ContinuousOn φ (Set.Icc s₁ s₂) :=
      hφD.continuousOn.mono (by
        intro x hx
        rw [Set.mem_Icc] at hx
        rw [Set.mem_Ioo]
        exact ⟨lt_of_lt_of_le hs₁a.1 hx.1, lt_of_le_of_lt hx.2 hs₂.2⟩)
    obtain ⟨s, hsIcc, hsφ⟩ :=
      intermediate_value_Icc (le_of_lt hs₁₂) hcont hmem
    refine ⟨s, ?_, hsφ⟩
    rw [Set.mem_Icc] at hsIcc
    rw [Set.mem_Ioo]
    exact ⟨lt_of_lt_of_le hs₁a.1 hsIcc.1, lt_of_le_of_lt hsIcc.2 hs₂.2⟩
  exact ⟨a, ha, hab, φ, hφD, hφderiv, hφsurj, eleft, eright⟩

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_isLocalDiffeomorphAt_symm_comp_of_mem_maximalAtlas](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
diffeomorphism. -/
private lemma omb_isLocalDiffeomorphAt_symm_comp_of_mem_maximalAtlas
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {X Y : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
  (e : OpenPartialHomeomorph X H) (he : e ∈ IsManifold.maximalAtlas I n X)
  (e' : OpenPartialHomeomorph Y H) (he' : e' ∈ IsManifold.maximalAtlas I n Y)
  (x : X) (hx : x ∈ e.source) (hmem : e x ∈ e'.target) :
  IsLocalDiffeomorphAt I I n (e'.symm ∘ e) x := by
  have hU : IsOpen (e.source ∩ e ⁻¹' e'.target) :=
    e.isOpen_inter_preimage e'.open_target
  have hV : IsOpen (e'.source ∩ e' ⁻¹' e.target) :=
    e'.isOpen_inter_preimage e.open_target
  have hf : Set.MapsTo (e'.symm ∘ e) (e.source ∩ e ⁻¹' e'.target)
    (e'.source ∩ e' ⁻¹' e.target) := by
    intro z hz
    obtain ⟨hzsrc, hztgt⟩ := hz
    rw [Set.mem_inter_iff]
    refine ⟨e'.map_target hztgt, ?_⟩
    rw [Set.mem_preimage, Function.comp_apply, e'.right_inv hztgt]
    exact e.map_source hzsrc
  have hf' : Set.MapsTo (e.symm ∘ e') (e'.source ∩ e' ⁻¹' e.target)
    (e.source ∩ e ⁻¹' e'.target) := by
    intro w hw
    obtain ⟨hwsrc, hwtgt⟩ := hw
    rw [Set.mem_inter_iff]
    refine ⟨e.map_target hwtgt, ?_⟩
    rw [Set.mem_preimage, Function.comp_apply, e.right_inv hwtgt]
    exact e'.map_source hwsrc
  have hleft : Set.LeftInvOn (e.symm ∘ e') (e'.symm ∘ e)
    (e.source ∩ e ⁻¹' e'.target) := by
    intro z hz
    obtain ⟨hzsrc, hztgt⟩ := hz
    simp only [Function.comp_apply, e'.right_inv hztgt, e.left_inv hzsrc]
  have hright : Set.RightInvOn (e.symm ∘ e') (e'.symm ∘ e)
    (e'.source ∩ e' ⁻¹' e.target) := by
    intro w hw
    obtain ⟨hwsrc, hwtgt⟩ := hw
    simp only [Function.comp_apply, e.right_inv hwtgt, e'.left_inv hwsrc]
  have h1U : ContMDiffOn I I n e (e.source ∩ e ⁻¹' e'.target) :=
    (contMDiffOn_of_mem_maximalAtlas he).mono Set.inter_subset_left
  have hfD : ContMDiffOn I I n (e'.symm ∘ e)
    (e.source ∩ e ⁻¹' e'.target) := by
    have h2 := contMDiffOn_symm_of_mem_maximalAtlas he'
    refine h2.comp h1U (by intro z hz; exact hz.2)
  have h1V : ContMDiffOn I I n e' (e'.source ∩ e' ⁻¹' e.target) :=
    (contMDiffOn_of_mem_maximalAtlas he').mono Set.inter_subset_left
  have hf'D : ContMDiffOn I I n (e.symm ∘ e')
    (e'.source ∩ e' ⁻¹' e.target) := by
    have h2 := contMDiffOn_symm_of_mem_maximalAtlas he
    refine h2.comp h1V (by intro w hw; exact hw.2)
  exact odm_isLocalDiffeomorphAt_of_invOn _ _ _ _ hU hV hf hf' ⟨hleft, hright⟩
    hfD hf'D x ⟨hx, hmem⟩

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_IccLeftChart_mem_maximalAtlas](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_IccLeftChart_mem_maximalAtlas :
  IccLeftChart (0 : ℝ) 1 ∈
    IsManifold.maximalAtlas (𝓡∂ 1) ∞ (Set.Icc (0 : ℝ) 1) := by
  have hbot : (⊥ : Set.Icc (0 : ℝ) 1).val < 1 := by
    rw [Set.Icc.coe_bot]
    norm_num
  have e : chartAt (EuclideanHalfSpace 1) (⊥ : Set.Icc (0 : ℝ) 1) =
    IccLeftChart 0 1 :=
    Icc_chartedSpaceChartAt_of_le_top hbot
  rw [← e]
  exact IsManifold.chart_mem_maximalAtlas _

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_IccRightChart_mem_maximalAtlas](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_IccRightChart_mem_maximalAtlas :
  IccRightChart (0 : ℝ) 1 ∈
    IsManifold.maximalAtlas (𝓡∂ 1) ∞ (Set.Icc (0 : ℝ) 1) := by
  have htop : (1 : ℝ) ≤ (⊤ : Set.Icc (0 : ℝ) 1).val := by
    rw [Set.Icc.coe_top]
  have e : chartAt (EuclideanHalfSpace 1) (⊤ : Set.Icc (0 : ℝ) 1) =
    IccRightChart 0 1 :=
    Icc_chartedSpaceChartAt_of_top_le htop
  rw [← e]
  exact IsManifold.chart_mem_maximalAtlas _

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[omb_isLocalDiffeomorphAt_Icc_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma omb_isLocalDiffeomorphAt_Icc_val (z : Set.Icc (0 : ℝ) 1)
  (h0 : 0 < z.val) (h1 : z.val < 1) :
  IsLocalDiffeomorphAt (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ Subtype.val z := by
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hU : IsOpen {z : Set.Icc (0 : ℝ) 1 | 0 < z.val ∧ z.val < 1} := by
    have e : {z : Set.Icc (0 : ℝ) 1 | 0 < z.val ∧ z.val < 1} =
      Subtype.val ⁻¹' Set.Ioo (0 : ℝ) 1 := rfl
    rw [e]
    exact isOpen_Ioo.preimage continuous_subtype_val
  have hV : IsOpen (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo
  have hf : Set.MapsTo Subtype.val
    {z : Set.Icc (0 : ℝ) 1 | 0 < z.val ∧ z.val < 1} (Set.Ioo (0 : ℝ) 1) := by
    intro z hz
    exact hz
  have hf' : Set.MapsTo (Set.projIcc 0 1 h01) (Set.Ioo (0 : ℝ) 1)
    {z : Set.Icc (0 : ℝ) 1 | 0 < z.val ∧ z.val < 1} := by
    intro u hu
    have hmem : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
    have e : (Set.projIcc 0 1 h01 u).val = u :=
      congrArg Subtype.val (Set.projIcc_of_mem h01 hmem)
    refine ⟨?_, ?_⟩
    · rw [e]
      exact hu.1
    · rw [e]
      exact hu.2
  have hleft : Set.LeftInvOn (Set.projIcc 0 1 h01) Subtype.val
    {z : Set.Icc (0 : ℝ) 1 | 0 < z.val ∧ z.val < 1} := by
    intro z hz
    have hmem : z.val ∈ Set.Icc (0 : ℝ) 1 := z.2
    have e : Set.projIcc 0 1 h01 z.val = ⟨z.val, hmem⟩ :=
      Set.projIcc_of_mem h01 hmem
    rw [e]
  have hright : Set.RightInvOn (Set.projIcc 0 1 h01) Subtype.val
    (Set.Ioo (0 : ℝ) 1) := by
    intro u hu
    have hmem : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
    exact congrArg Subtype.val (Set.projIcc_of_mem h01 hmem)
  have hval : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞
    (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) := contMDiff_subtypeVal_Icc
  have hfD : ContMDiffOn (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ Subtype.val
    {z : Set.Icc (0 : ℝ) 1 | 0 < z.val ∧ z.val < 1} :=
    (contMDiffOn_univ.mpr hval).mono (Set.subset_univ _)
  have hproj : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (Set.projIcc 0 1 h01)
    (Set.Icc (0 : ℝ) 1) := contMDiffOn_projIcc
  have hf'D : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (Set.projIcc 0 1 h01)
    (Set.Ioo (0 : ℝ) 1) :=
    hproj.mono Set.Ioo_subset_Icc_self
  exact odm_isLocalDiffeomorphAt_of_invOn _ _ _ _ hU hV hf hf' ⟨hleft, hright⟩
    hfD hf'D z ⟨h0, h1⟩

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[ombGlueF_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma ombGlueF_of_lt (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
  (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
  (q p : M) (a : ℝ) (φ : ℝ → ℝ) (z : Set.Icc (0 : ℝ) 1) (h : z.val < a) :
  ombGlueF M Ψ q p a φ z = ombHalfCurve M q z.val := by
  classical
  unfold ombGlueF
  rw [ite_eq_left h]

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[ombGlueF_of_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma ombGlueF_of_gt (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
  (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
  (q p : M) (a : ℝ) (φ : ℝ → ℝ) (z : Set.Icc (0 : ℝ) 1)
  (h1 : ¬ z.val < a) (h2 : 1 - a < z.val) :
  ombGlueF M Ψ q p a φ z = ombHalfCurve M p (1 - z.val) := by
  classical
  unfold ombGlueF
  rw [ite_eq_right h1, ite_eq_left h2]

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[ombGlueF_of_mid](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma ombGlueF_of_mid (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
  (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
  (q p : M) (a : ℝ) (φ : ℝ → ℝ) (z : Set.Icc (0 : ℝ) 1)
  (h1 : ¬ z.val < a) (h2 : ¬ 1 - a < z.val) :
  ombGlueF M Ψ q p a φ z = ombValPsi M Ψ (φ z.val) := by
  classical
  unfold ombGlueF
  rw [ite_eq_right h1, ite_eq_right h2]

end MathlibExt.Geometry.Manifold.OneDimensionalWanted

/--
[compact_connected_one_manifold_with_boundary_classification](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma compact_connected_one_manifold_with_boundary_classification_eq
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M] :
-- imply
  Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡 1⟯ Circle) ∨ Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ (Set.Icc (0 : ℝ) 1)) := by
-- proof
  apply MathlibExt.Geometry.Manifold.OneDimensionalWanted.compact_connected_one_manifold_with_boundary_classification M


-- created on 2026-10-20
-- updated on 2026-10-26
