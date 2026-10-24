import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.ParametricSard
open MeasureTheory
open MathlibExt.Geometry.Manifold.ParametricSardWanted


namespace MathlibExt.Geometry.Manifold.ParametricSardWanted

/--
[slice_fderiv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ParametricSard.lean)
-/
@[path]
inclusion. -/
private lemma slice_fderiv_eq {p m n : ℕ}
  (F : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
  (hF : ContDiff ℝ ⊤ F) (a : EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin m)) :
  fderiv ℝ (fun x : EuclideanSpace ℝ (Fin m) => F (a, x)) x =
    (fderiv ℝ F (a, x)).comp (ContinuousLinearMap.inr ℝ _ _) := by
  have hdiff : Differentiable ℝ F := hF.differentiable (by simp)
  have h1 : HasFDerivAt F (fderiv ℝ F (a, x)) (a, x) := (hdiff (a, x)).hasFDerivAt
  have h2 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin m) => (a, x))
    (ContinuousLinearMap.inr ℝ _ _) x :=
    hasFDerivAt_prodMk_right a x
  have hcomp := HasFDerivAt.comp x h1 h2
  have hfun : (F ∘ fun x : EuclideanSpace ℝ (Fin m) => (a, x)) =
    (fun x : EuclideanSpace ℝ (Fin m) => F (a, x)) := rfl
  rwa [hfun] at hcomp

end MathlibExt.Geometry.Manifold.ParametricSardWanted

namespace MathlibExt.Geometry.Manifold.ParametricSardWanted

/--
[badParameterSet_eq_image](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ParametricSard.lean)
-/
@[path]
private lemma badParameterSet_eq_image {p m n : ℕ}
  (F : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
  (y : EuclideanSpace ℝ (Fin n)) :
  badParameterSet (F := F) (y := y) = Prod.fst '' fibSing F y := by
  ext a
  simp only [badParameterSet, fibSing, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨x, hFx, hnsurj⟩
    exact ⟨(a, x), ⟨hFx, hnsurj⟩, rfl⟩
  · rintro ⟨⟨a', x⟩, ⟨hFx, hnsurj⟩, hfst⟩
    have hfst' : a' = a := hfst
    subst hfst'
    refine ⟨x, hFx, ?_⟩
    simpa using hnsurj

end MathlibExt.Geometry.Manifold.ParametricSardWanted

namespace MathlibExt.Geometry.Manifold.ParametricSardWanted

/--
[slice_surj_iff_ker_fst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ParametricSard.lean)
-/
@[path]
the kernel of `L`. -/
private lemma slice_surj_iff_ker_fst {E₁ E₂ F₁ : Type*} [NormedAddCommGroup E₁]
  [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] (L : E₁ × E₂ →L[ℝ] F₁)
  (hL : Function.Surjective L) :
  Function.Surjective (L.comp (ContinuousLinearMap.inr ℝ E₁ E₂)) ↔
    ∀ v : E₁, ∃ w : E₂, L (v, w) = 0 := by
  constructor
  · intro hsurj v
    obtain ⟨w, hw⟩ := hsurj (-L (v, 0))
    refine ⟨w, ?_⟩
    have hvw : (v, w) = (v, 0) + (0, w) := by ext <;> simp
    have hLvw : L (v, w) = L (v, 0) + L (0, w) := by rw [hvw, map_add]
    have h0w : L (0, w) = -L (v, 0) := by
      have hw' : (L.comp (ContinuousLinearMap.inr ℝ E₁ E₂)) w = -L (v, 0) := hw
      simpa using hw'
    rw [hLvw, h0w, add_neg_cancel]
  · intro hker u
    obtain ⟨⟨v, w⟩, hvw⟩ := hL u
    obtain ⟨w', hw'⟩ := hker v
    refine ⟨w - w', ?_⟩
    have hsub : ((0, w - w') : E₁ × E₂) = (v, w) - (v, w') := by ext <;> simp
    have hLsub : L (0, w - w') = L (v, w) - L (v, w') := by rw [hsub, map_sub]
    have hgoal : (L.comp (ContinuousLinearMap.inr ℝ E₁ E₂)) (w - w') = u := by
      have hcomp : (L.comp (ContinuousLinearMap.inr ℝ E₁ E₂)) (w - w') = L (0, w - w') :=
        rfl
      rw [hcomp, hLsub, hvw, hw', sub_zero]
    exact hgoal

end MathlibExt.Geometry.Manifold.ParametricSardWanted

namespace MathlibExt.Geometry.Manifold.ParametricSardWanted

/--
[range_chartDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ParametricSard.lean)
-/
@[path]
components of kernel elements. -/
private lemma range_chartDeriv {E₁ E₂ F₁ : Type*} [NormedAddCommGroup E₁]
  [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] {K : Type*} [NormedAddCommGroup K]
  [NormedSpace ℝ K]
  (D : E₁ × E₂ →L[ℝ] F₁) (P : E₁ × E₂ →L[ℝ] K) (e : (E₁ × E₂) ≃L[ℝ] (F₁ × K))
  (he : ∀ z, e z = (D z, P z)) :
  Set.range (fun w : K => (e.symm (0, w)).1) = { v : E₁ | ∃ w : E₂, D (v, w) = 0 } := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨(e.symm (0, w)).2, ?_⟩
    have h1 : e (e.symm (0, w)) = (0, w) := e.apply_symm_apply _
    have h2 : e (e.symm (0, w)) = (D (e.symm (0, w)), P (e.symm (0, w))) := he _
    rw [h2] at h1
    have hD : D (e.symm (0, w)) = 0 := congrArg Prod.fst h1
    have h3 : D ((e.symm (0, w)).1, (e.symm (0, w)).2) = 0 := by
      rwa [Prod.mk.eta]
    exact h3
  · rintro ⟨w, hw⟩
    refine ⟨P (v, w), ?_⟩
    have h3 : e (v, w) = (0, P (v, w)) := by
      have h := he (v, w)
      rwa [hw] at h
    have h4 : e.symm (0, P (v, w)) = (v, w) := by
      have h5 : e.symm (e (v, w)) = (v, w) := e.symm_apply_apply _
      rwa [h3] at h5
    change (e.symm (0, P (v, w))).1 = v
    rw [h4]

end MathlibExt.Geometry.Manifold.ParametricSardWanted

namespace MathlibExt.Geometry.Manifold.ParametricSardWanted

/--
[chartEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ParametricSard.lean)
-/
@[path]
equivalence. -/
private lemma chartEquiv {E₁ E₂ F₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [FiniteDimensional ℝ F₁]
  (D : E₁ × E₂ →L[ℝ] F₁) (hD : Function.Surjective D) (K : Submodule ℝ (E₁ × E₂))
  (hK : K = LinearMap.ker (D : E₁ × E₂ →ₗ[ℝ] F₁)) (P : E₁ × E₂ →L[ℝ] ↥K)
  (hP : ∀ x : ↥K, P ↑x = x) :
  ∃ e : (E₁ × E₂) ≃L[ℝ] (F₁ × ↥K), ∀ z, e z = (D z, P z) := by
  have hTinj : Function.Injective (D.prod P : E₁ × E₂ →L[ℝ] F₁ × ↥K) := by
    intro v w hvw
    have hker : ∀ v, (D.prod P) v = 0 → v = 0 := by
      intro v hv
      have h1 : D v = 0 := congrArg Prod.fst hv
      have h2 : P v = 0 := congrArg Prod.snd hv
      have hvmem : v ∈ K := by
        rw [hK]
        exact LinearMap.mem_ker.mpr h1
      have hPid : P v = ⟨v, hvmem⟩ := hP ⟨v, hvmem⟩
      rw [h2] at hPid
      have hval : ((0 : ↥K) : E₁ × E₂) = v := congrArg Subtype.val hPid
      simpa using hval.symm
    have hsub : v - w = 0 := hker (v - w) (by rw [map_sub, hvw, sub_self])
    exact sub_eq_zero.mp hsub
  have hdim : Module.finrank ℝ (E₁ × E₂) = Module.finrank ℝ (F₁ × ↥K) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (D : E₁ × E₂ →ₗ[ℝ] F₁)
    have hrange : LinearMap.range (D : E₁ × E₂ →ₗ[ℝ] F₁) = ⊤ :=
      LinearMap.range_eq_top.mpr hD
    have hfin : Module.finrank ℝ ↥(LinearMap.range (D : E₁ × E₂ →ₗ[ℝ] F₁)) =
      Module.finrank ℝ F₁ := by
      rw [hrange]
      exact LinearEquiv.finrank_eq Submodule.topEquiv
    rw [← hK] at h1
    simp only [Module.finrank_prod] at h1 ⊢
    omega
  have hTinj' : Function.Injective (D.prod P : E₁ × E₂ →ₗ[ℝ] F₁ × ↥K) := hTinj
  refine ⟨(LinearMap.linearEquivOfInjective _ hTinj' hdim).toContinuousLinearEquiv, ?_⟩
  intro z
  rfl

end MathlibExt.Geometry.Manifold.ParametricSardWanted

namespace MathlibExt.Geometry.Manifold.ParametricSardWanted

/--
[local_null_at](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ParametricSard.lean)
-/
@[path]
private lemma local_null_at {p m n : ℕ}
  (F : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
  (y : EuclideanSpace ℝ (Fin n)) (hF : ContDiff ℝ ⊤ F)
  (hreg : ∀ a x, F (a, x) = y → Function.Surjective (fderiv ℝ F (a, x)))
  (z0 : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m)) (hz0 : F z0 = y) :
  ∃ V ∈ nhds z0, volume (Prod.fst '' (V ∩ fibSing F y)) = 0 := by
  have hL0 : Function.Surjective (fderiv ℝ F z0) := by
    have hF0 : F (z0.1, z0.2) = y := by
      rwa [Prod.mk.eta]
    have h := hreg z0.1 z0.2 hF0
    rwa [Prod.mk.eta] at h
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m)) :=
    LinearMap.ker (↑(fderiv ℝ F z0) : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m)
      →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) with hKdef
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional K
  obtain ⟨e, he⟩ := chartEquiv (fderiv ℝ F z0) hL0 K hKdef P hP
  have heq : (e : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m) →L[ℝ]
    EuclideanSpace ℝ (Fin n) × ↥K) = (fderiv ℝ F z0).prod P := by
    rw [ContinuousLinearMap.ext_iff]
    intro v
    exact he v
  have hΦsmooth : ContDiff ℝ ⊤ (fun z : EuclideanSpace ℝ (Fin p) ×
    EuclideanSpace ℝ (Fin m) => (F z, P z)) :=
    hF.prodMk P.contDiff
  have hΦ'd : ∀ z, HasFDerivAt (fun z : EuclideanSpace ℝ (Fin p) ×
    EuclideanSpace ℝ (Fin m) => (F z, P z)) ((fderiv ℝ F z).prod P) z := fun z =>
    ((hF.differentiable (by simp) z).hasFDerivAt.prodMk P.hasFDerivAt)
  have hfderivΦ : ∀ z, fderiv ℝ (fun z : EuclideanSpace ℝ (Fin p) ×
    EuclideanSpace ℝ (Fin m) => (F z, P z)) z = (fderiv ℝ F z).prod P :=
    fun z => (hΦ'd z).fderiv
  have hstrict : HasStrictFDerivAt (fun z : EuclideanSpace ℝ (Fin p) ×
    EuclideanSpace ℝ (Fin m) => (F z, P z))
    (e : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin n) × ↥K) z0 := by
    apply ContDiffAt.hasStrictFDerivAt' hΦsmooth.contDiffAt _ (by simp)
    rw [heq]
    exact hΦ'd z0
  set Φh : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin n) × ↥K) := hstrict.toOpenPartialHomeomorph _ with hΦhdef
  have hΦh_coe : (Φh : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m) →
    EuclideanSpace ℝ (Fin n) × ↥K) = (fun z => (F z, P z)) :=
    hstrict.toOpenPartialHomeomorph_coe
  have hz0src : z0 ∈ Φh.source := hstrict.mem_toOpenPartialHomeomorph_source
  set O : Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m)) :=
    fderiv ℝ (fun z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m) => (F z, P z)) ⁻¹'
      Set.range ((↑) : ((EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m)) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin n) × ↥K)) → _ →L[ℝ] _) with hOdef
  have hO : IsOpen O := by
    have hcont : Continuous (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin p) ×
      EuclideanSpace ℝ (Fin m) => (F z, P z))) :=
      hΦsmooth.continuous_fderiv (by simp)
    exact ContinuousLinearEquiv.isOpen.preimage hcont
  have hz0O : z0 ∈ O := ⟨e, by rw [hfderivΦ]; exact heq⟩
  set V : Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m)) :=
    Φh.source ∩ O with hVdef
  have hV : IsOpen V := Φh.open_source.inter hO
  have hz0V : z0 ∈ V := ⟨hz0src, hz0O⟩
  set c : ↥K → EuclideanSpace ℝ (Fin n) × ↥K := fun k => (y, k) with hcdef
  have hc_cont : Continuous c := continuous_const.prodMk continuous_id
  set Tgt : Set (EuclideanSpace ℝ (Fin n) × ↥K) := Φh.target ∩ Φh.symm ⁻¹' O with hTgtdef
  have hTgt : IsOpen Tgt :=
    Φh.continuousOn_symm.isOpen_inter_preimage Φh.open_target hO
  set U : Set ↥K := c ⁻¹' Tgt with hUdef
  have hU : IsOpen U := hTgt.preimage hc_cont
  set g : ↥K → EuclideanSpace ℝ (Fin p) := Prod.fst ∘ Φh.symm ∘ c with hgdef
  have hg_smooth : ContDiffOn ℝ ⊤ g U := by
    intro k hk
    have hmem : (y, k) ∈ Φh.target := (hk : c k ∈ Tgt).1
    have hOmem : Φh.symm (y, k) ∈ O := (hk : c k ∈ Tgt).2
    obtain ⟨e', he'⟩ := hOmem
    have hderivΦ : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin p) ×
      EuclideanSpace ℝ (Fin m) => (F z, P z)) (e' : _ →L[ℝ] _) (Φh.symm (y, k)) := by
      have hbase := hΦ'd (Φh.symm (y, k))
      have hTe : (e' : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m) →L[ℝ]
        EuclideanSpace ℝ (Fin n) × ↥K) =
        (fderiv ℝ F (Φh.symm (y, k))).prod P := he'.trans (hfderivΦ _)
      rwa [hTe]
    have hsymm : ContDiffAt ℝ ⊤ Φh.symm (y, k) :=
      Φh.contDiffAt_symm hmem hderivΦ hΦsmooth.contDiffAt
    have hc_at : ContDiffAt ℝ ⊤ c k := contDiffAt_const.prodMk contDiffAt_id
    have hcomp1 : ContDiffAt ℝ ⊤ (Φh.symm ∘ c) k := hsymm.comp k hc_at
    have hcomp2 : ContDiffAt ℝ ⊤ (Prod.fst ∘ (Φh.symm ∘ c)) k :=
      contDiffAt_fst.comp k hcomp1
    exact hcomp2.contDiffWithinAt
  have hsub : Prod.fst '' (V ∩ fibSing F y) ⊆
    g '' { k : ↥K | k ∈ U ∧ ¬ Function.Surjective (fderiv ℝ g k) } := by
    rintro a ⟨z, ⟨hzV, hzS⟩, rfl⟩
    have hzsrc : z ∈ Φh.source := hzV.1
    have hzO : z ∈ O := hzV.2
    have hFz : F z = y := hzS.1
    set k : ↥K := P z with hkdef
    have hΦz : Φh z = (y, k) := by
      have h1 : Φh z = (F z, P z) := by rw [hΦh_coe]
      rw [h1, hFz]
    have htgt : (y, k) ∈ Φh.target := by
      have h := Φh.map_source hzsrc
      rwa [hΦz] at h
    have hψ : Φh.symm (y, k) = z := by
      have h := Φh.left_inv hzsrc
      rwa [hΦz] at h
    have h2 : Φh.symm (y, k) ∈ O := by
      rwa [hψ]
    have hkU : k ∈ U := ⟨htgt, h2⟩
    have hgk : g k = z.1 := by
      have h1 : g k = (Φh.symm (y, k)).1 := rfl
      rw [h1, hψ]
    have hcrit : ¬ Function.Surjective (fderiv ℝ g k) := by
      obtain ⟨e', he'z⟩ := hzO
      set e'sym := (e'.symm : EuclideanSpace ℝ (Fin n) × ↥K →L[ℝ]
        EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m)) with he'sdef
      have hDz : Function.Surjective (fderiv ℝ F z) := by
        have hF0 : F (z.1, z.2) = y := by
          rwa [Prod.mk.eta]
        have h := hreg z.1 z.2 hF0
        rwa [Prod.mk.eta] at h
      have hslice : ¬ Function.Surjective (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin m) =>
        F (z.1, x)) z.2) := hzS.2
      set J : ↥K →L[ℝ] (EuclideanSpace ℝ (Fin n) × ↥K) :=
        (0 : ↥K →L[ℝ] EuclideanSpace ℝ (Fin n)).prod
          (ContinuousLinearMap.id ℝ ↥K) with hJdef
      have hcJ : HasFDerivAt c J k :=
        (hasFDerivAt_const y k).prodMk (hasFDerivAt_id k)
      have hsymm_deriv : HasFDerivAt Φh.symm e'sym (y, k) :=
        Φh.hasFDerivAt_symm (f' := e') htgt (by
          have hbase := hΦ'd z
          have hTe : (e' : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m) →L[ℝ]
            EuclideanSpace ℝ (Fin n) × ↥K) = (fderiv ℝ F z).prod P :=
            he'z.trans (hfderivΦ z)
          rw [hΦh_coe, hTe, hψ]
          exact hbase)
      have hcompm : HasFDerivAt (Φh.symm ∘ c) (e'sym.comp J) k :=
        HasFDerivAt.comp k hsymm_deriv hcJ
      have hfull : HasFDerivAt g ((ContinuousLinearMap.fst ℝ _ _).comp (e'sym.comp J)) k :=
        HasFDerivAt.comp k hasFDerivAt_fst hcompm
      have hfderivg : fderiv ℝ g k =
        (ContinuousLinearMap.fst ℝ _ _).comp (e'sym.comp J) := hfull.fderiv
      have hgw : ∀ w : ↥K, fderiv ℝ g k w = (e'.symm (0, w)).1 :=
        fun w => (congrArg (· w) hfderivg).trans (by rfl)
      have he'fun : ∀ u, e' u = ((fderiv ℝ F z) u, P u) := by
        intro u
        have h := congrArg (fun L : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m)
          →L[ℝ] EuclideanSpace ℝ (Fin n) × ↥K => L u) he'z
        rw [hfderivΦ] at h
        simpa using h
      have hrange := range_chartDeriv (fderiv ℝ F z) P e' he'fun
      intro hsurj
      have hkerfst : ∀ v : EuclideanSpace ℝ (Fin p), ∃ w : EuclideanSpace ℝ (Fin m),
        (fderiv ℝ F z) (v, w) = 0 := by
        intro v
        have hmem : v ∈ Set.range (fun w : ↥K => (e'.symm (0, w)).1) := by
          obtain ⟨w, hw⟩ := hsurj v
          refine ⟨w, ?_⟩
          change (e'.symm (0, w)).1 = v
          rwa [← hgw w]
        rwa [hrange] at hmem
      apply hslice
      rw [slice_fderiv_eq F hF z.1 z.2]
      have hDz' : fderiv ℝ F (z.1, z.2) = fderiv ℝ F z := by rw [Prod.mk.eta]
      rw [hDz']
      exact (slice_surj_iff_ker_fst _ hDz).mpr hkerfst
    have hkmem : k ∈ U ∧ ¬ Function.Surjective (fderiv ℝ g k) := ⟨hkU, hcrit⟩
    exact ⟨k, hkmem, hgk⟩
  have hcrit_null : volume
    (g '' { k : ↥K | k ∈ U ∧ ¬ Function.Surjective (fderiv ℝ g k) }) = 0 :=
    MathlibExt.Geometry.Manifold.SardWanted.sard_euclidean_open ↥K
      (EuclideanSpace ℝ (Fin p)) volume U hU g (hg_smooth.of_le le_top)
  have hVnull : volume (Prod.fst '' (V ∩ fibSing F y)) = 0 :=
    measure_mono_null hsub hcrit_null
  exact ⟨V, hV.mem_nhds hz0V, hVnull⟩

end MathlibExt.Geometry.Manifold.ParametricSardWanted

namespace MathlibExt.Geometry.Manifold.ParametricSardWanted

/--
[parametricSard](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ParametricSard.lean)
-/
@[path]
lemma parametricSard
  {p m n : ℕ}
  {F : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
  {y : EuclideanSpace ℝ (Fin n)}
-- given
  (hF : ContDiff ℝ ⊤ F)
  (hreg : ∀ a x, F (a, x) = y → Function.Surjective (fderiv ℝ F (a, x))) :
-- imply
  volume (badParameterSet (F := by
-- proof
  rwa [badParameterSet_eq_image]
    (fun z0 hz0 => local_null_at F y hF hreg z0 hz0.1)

end MathlibExt.Geometry.Manifold.ParametricSardWanted


-- created on 2026-10-20
-- updated on 2026-10-23
