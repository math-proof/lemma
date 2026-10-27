import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Topology.Algebra.PeterWeyl.Part6
open MeasureTheory
open scoped ComplexInnerProductSpace ComplexConjugate BoundedContinuousFunction
open MathlibExt.Topology.Algebra.PeterWeylWanted


namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwTransl_ae](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwTransl_ae (g : G) (f : Lp ℂ 2 (pwHaar G)) :
  ((pwTransl (G := G) g f : Lp ℂ 2 (pwHaar G)) : G → ℂ)
    =ᵐ[pwHaar G] ((f : Lp ℂ 2 (pwHaar G)) : G → ℂ) ∘ (fun x => g⁻¹ * x) :=
  Lp.coeFn_compMeasurePreserving _ _

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwTransl_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwTransl_mul (g h : G) (f : Lp ℂ 2 (pwHaar G)) :
  pwTransl (G := G) (g * h) f = pwTransl (G := G) g (pwTransl (G := G) h f) := by
  apply Lp.ext
  have h1 := pwTransl_ae (G := G) (g * h) f
  have h2 := pwTransl_ae (G := G) g (pwTransl (G := G) h f)
  have h3 := pwTransl_ae (G := G) h f
  have hq := (measurePreserving_mul_left (pwHaar G) g⁻¹).quasiMeasurePreserving
  have h4 := hq.ae_eq_comp h3
  have h6 : ((((f : Lp ℂ 2 (pwHaar G)) : G → ℂ)) ∘ (fun x => h⁻¹ * x)) ∘
    (fun x => g⁻¹ * x)
    = (((f : Lp ℂ 2 (pwHaar G)) : G → ℂ)) ∘ (fun x => (g * h)⁻¹ * x) := by
    funext x
    simp only [Function.comp_apply]
    congr 1
    rw [mul_inv_rev, mul_assoc]
  rw [h6] at h4
  exact h1.trans (h2.trans h4).symm

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwTransl_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwTransl_one (f : Lp ℂ 2 (pwHaar G)) :
  pwTransl (G := G) 1 f = f := by
  apply Lp.ext
  have h1 := pwTransl_ae (G := G) 1 f
  have hfun : (((f : Lp ℂ 2 (pwHaar G)) : G → ℂ)) ∘ (fun x : G => (1 : G)⁻¹ * x)
    = ((f : Lp ℂ 2 (pwHaar G)) : G → ℂ) := by
    funext x
    simp only [Function.comp_apply, inv_one, one_mul]
  rwa [hfun] at h1

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwTransl_inner](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwTransl_inner (g : G) (u v : Lp ℂ 2 (pwHaar G)) :
  ⟪pwTransl (G := G) g u, v⟫ = ⟪u, pwTransl (G := G) g⁻¹ v⟫ := by
  have h : v = pwTransl (G := G) g (pwTransl (G := G) g⁻¹ v) := by
    rw [← pwTransl_mul, mul_inv_cancel, pwTransl_one]
  conv_lhs => rw [h]
  exact LinearIsometry.inner_map_map (pwTransl (G := G) g) u
    (pwTransl (G := G) g⁻¹ v)

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwTransl_inner'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwTransl_inner' (g : G) (u v : Lp ℂ 2 (pwHaar G)) :
  ⟪u, pwTransl (G := G) g v⟫ = ⟪pwTransl (G := G) g⁻¹ u, v⟫ := by
  rw [pwTransl_inner, inv_inv]

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwTransl_toLp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwTransl_toLp (F : C(G, ℂ)) (g : G) :
  pwTransl (G := G) g (ContinuousMap.toLp 2 (pwHaar G) ℂ F)
    = ContinuousMap.toLp 2 (pwHaar G) ℂ
      (F.comp ⟨fun t => g⁻¹ * t, continuous_const_mul g⁻¹⟩) := by
  apply Lp.ext
  have h1 := pwTransl_ae (G := G) g (ContinuousMap.toLp 2 (pwHaar G) ℂ F)
  have hF : ((ContinuousMap.toLp 2 (pwHaar G) ℂ F : Lp ℂ 2 (pwHaar G)) : G → ℂ)
    =ᵐ[pwHaar G] (F : C(G, ℂ)) := ContinuousMap.coeFn_toLp (pwHaar G) F
  have hq := (measurePreserving_mul_left (pwHaar G) g⁻¹).quasiMeasurePreserving
  have h4 := hq.ae_eq_comp hF
  have h5 : ((ContinuousMap.toLp 2 (pwHaar G) ℂ
    (F.comp ⟨fun t => g⁻¹ * t, continuous_const_mul g⁻¹⟩) : Lp ℂ 2 (pwHaar G)) :
    G → ℂ)
    =ᵐ[pwHaar G] ((F : C(G, ℂ)) ∘ (fun t => g⁻¹ * t)) :=
    ContinuousMap.coeFn_toLp (pwHaar G) _
  exact h1.trans (h4.trans h5.symm)

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwTransl_toLp_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwTransl_toLp_continuous (F : C(G, ℂ)) :
  Continuous (fun g => pwTransl (G := G) g
    (ContinuousMap.toLp 2 (pwHaar G) ℂ F)) := by
  have hK : Continuous (fun p : G × G => F (p.1⁻¹ * p.2)) :=
    F.continuous.comp (continuous_fst.inv.mul continuous_snd)
  have hfun : (fun g => pwTransl (G := G) g (ContinuousMap.toLp 2 (pwHaar G) ℂ F))
    = ⇑(ContinuousMap.toLp 2 (pwHaar G) ℂ) ∘
      ⇑(⟨fun p : G × G => F (p.1⁻¹ * p.2), hK⟩ : C(G × G, ℂ)).curry := by
    funext g
    simp only [Function.comp_apply]
    rw [pwTransl_toLp]
    congr 1
  rw [hfun]
  exact (ContinuousMap.toLp 2 (pwHaar G) ℂ).continuous.comp
    (⟨fun p : G × G => F (p.1⁻¹ * p.2), hK⟩ : C(G × G, ℂ)).curry.continuous

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwPhiKer_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
private lemma pwPhiKer_apply (k : C(G, ℂ)) (g h : G) :
  (pwPhiKer (G := G) k g) h = conj (k (h⁻¹ * g)) :=
  rfl

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwE_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
omit [Group G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
private lemma pwE_apply (F : C(G, ℂ)) (x : G) :
  ((ContinuousMap.isometryEquivBoundedOfCompact G ℂ) F) x = F x := by
  rw [ContinuousMap.isometryEquivBoundedOfCompact_apply,
    BoundedContinuousFunction.mkOfCompact_apply]

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwA_mem_obtain](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwA_mem_obtain (k : C(G, ℂ)) (Y : G →ᵇ ℂ) (hY : Y ∈ pwA (G := G) k) :
  ∃ f : Lp ℂ 2 (pwHaar G), f ∈ Metric.closedBall (0 : Lp ℂ 2 (pwHaar G)) 1 ∧
    ∀ x : G, Y x = (pwT0Map (G := G) k f) x := by
  obtain ⟨F', hF', hFY⟩ := hY
  obtain ⟨f, hfball, hFf⟩ := hF'
  refine ⟨f, hfball, fun x => ?_⟩
  rw [← hFY, ← hFf]
  exact pwE_apply (G := G) _ x

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwTransl_Phi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwTransl_Phi (k : C(G, ℂ)) (a g : G) :
  pwTransl (G := G) a⁻¹ (pwPhi (G := G) k g) = pwPhi (G := G) k (a⁻¹ * g) := by
  unfold pwPhi
  rw [pwTransl_toLp]
  congr 1
  apply ContinuousMap.ext
  intro h
  simp only [ContinuousMap.comp_apply, pwPhiKer_apply]
  change conj (k (((a⁻¹)⁻¹ * h)⁻¹ * g)) = conj (k (h⁻¹ * (a⁻¹ * g)))
  congr 1
  congr 1
  rw [inv_inv, mul_inv_rev, mul_assoc]

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwS_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwS_symmetric (k : C(G, ℂ)) :
  LinearMap.IsSymmetric ((pwS (G := G) k) :
    Lp ℂ 2 (pwHaar G) →ₗ[ℂ] Lp ℂ 2 (pwHaar G)) := by
  have hS : pwS (G := G) k
    = star (pwT (G := G) k) * (pwT (G := G) k) := by
    unfold pwS
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
  rwa [hS]
    (IsSelfAdjoint.star_mul_self _)

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwBump](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwBump {z : G} (hz : z ≠ 1) :
  ∃ k : C(G, ℂ), (∫ h, k h * k (h⁻¹) ∂(pwHaar G)) ≠ 0 ∧
    ∀ h : G, k h * k (h⁻¹ * z⁻¹) = 0 := by
  have hzinv : z⁻¹ ≠ 1 := inv_ne_one.mpr hz
  have h1W : (1 : G) ∈ (({z⁻¹} : Set G)ᶜ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact Ne.symm hzinv
  have hWopen : IsOpen (({z⁻¹} : Set G)ᶜ) := isOpen_compl_singleton
  obtain ⟨V, hVopen, h1V, hVV⟩ :=
    exists_open_nhds_one_mul_subset (hWopen.mem_nhds h1W)
  have hdis : Disjoint (Vᶜ) ({1} : Set G) := by
    rw [Set.disjoint_left]
    intro x hxV hx1
    rw [Set.mem_singleton_iff] at hx1
    subst hx1
    exact hxV h1V
  obtain ⟨f, hf0, hf1, hfb⟩ := exists_continuous_zero_one_of_isClosed
    hVopen.isClosed_compl isClosed_singleton hdis
  have hf1v : f 1 = 1 := hf1 (Set.mem_singleton 1)
  set k : C(G, ℂ) := ⟨fun x => ((f x : ℝ) : ℂ),
    Complex.continuous_ofReal.comp f.continuous⟩ with hkdef
  have hk : ∀ x : G, k x = ((f x : ℝ) : ℂ) := fun x => rfl
  refine ⟨k, ?_, ?_⟩
  · have fcont : Continuous (fun h => f h * f h⁻¹) :=
    f.continuous.mul (f.continuous.comp continuous_inv)
    have fcomp : HasCompactSupport (fun h => f h * f h⁻¹) :=
      HasCompactSupport.of_compactSpace _
    have hnn : 0 ≤ fun h => f h * f h⁻¹ := by
      intro h
      exact mul_nonneg (Set.mem_Icc.mp (hfb h)).1
        (Set.mem_Icc.mp (hfb h⁻¹)).1
    have h1v : (fun h => f h * f h⁻¹) 1 ≠ 0 := by
      change f 1 * f 1⁻¹ ≠ 0
      rwa [hf1v, inv_one, hf1v, one_mul]
    have hpos : 0 < ∫ h, f h * f h⁻¹ ∂(pwHaar G) :=
      fcont.integral_pos_of_hasCompactSupport_nonneg_nonzero fcomp hnn h1v
    have hci : (∫ h, k h * k h⁻¹ ∂(pwHaar G))
      = ((∫ h, f h * f h⁻¹ ∂(pwHaar G) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards with h
      rw [hk h, hk h⁻¹, Complex.ofReal_mul]
    rw [hci]
    exact_mod_cast ne_of_gt hpos
  · intro h
    rw [hk h, hk (h⁻¹ * z⁻¹)]
    by_cases hh : f h = 0
    · rw [hh]
      simp
    · by_cases hh2 : f (h⁻¹ * z⁻¹) = 0
      · rw [hh2]
        simp
      · have hhV : h ∈ V := by
        by_contra hc
        exact hh (hf0 hc)
        have hhV2 : h⁻¹ * z⁻¹ ∈ V := by
          by_contra hc
          exact hh2 (hf0 hc)
        have hmem := Set.mul_mem_mul hhV hhV2
        rw [mul_inv_cancel_left] at hmem
        have hcon : z⁻¹ ∈ (({z⁻¹} : Set G)ᶜ) := hVV hmem
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hcon
        exact (hcon trivial).elim

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwU_coe](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwU_coe (E : Submodule ℂ (Lp ℂ 2 (pwHaar G)))
  (hinv : ∀ (g : G) (v : Lp ℂ 2 (pwHaar G)),
    v ∈ E → pwTransl (G := G) g v ∈ E)
  (g : G) (x : ↥E) :
  ((pwU (G := G) E hinv g x : ↥E) : Lp ℂ 2 (pwHaar G))
    = pwTransl (G := G) g (x : Lp ℂ 2 (pwHaar G)) := by
  unfold pwU
  simp only [LinearMap.coe_restrict_apply, LinearIsometry.coe_toLinearMap]

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwU_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwU_mul (E : Submodule ℂ (Lp ℂ 2 (pwHaar G)))
  (hinv : ∀ (g : G) (v : Lp ℂ 2 (pwHaar G)),
    v ∈ E → pwTransl (G := G) g v ∈ E)
  (g h : G) : pwU (G := G) E hinv (g * h)
    = pwU (G := G) E hinv g * pwU (G := G) E hinv h := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [pwU_coe, Module.End.mul_apply, pwU_coe, pwU_coe, pwTransl_mul]

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwU_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwU_one (E : Submodule ℂ (Lp ℂ 2 (pwHaar G)))
  (hinv : ∀ (g : G) (v : Lp ℂ 2 (pwHaar G)),
    v ∈ E → pwTransl (G := G) g v ∈ E) :
  pwU (G := G) E hinv 1 = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [pwU_coe]
  exact pwTransl_one _

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwRep_entry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwRep_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
  (E : Submodule ℂ (Lp ℂ 2 (pwHaar G)))
  (hinv : ∀ (g : G) (v : Lp ℂ 2 (pwHaar G)),
    v ∈ E → pwTransl (G := G) g v ∈ E)
  (b : OrthonormalBasis ι ℂ ↥E) (g : G) (i j : ι) :
  LinearMap.toMatrix b.toBasis b.toBasis (pwU (G := G) E hinv g) i j
    = ⟪((b i : ↥E) : Lp ℂ 2 (pwHaar G)),
      pwTransl (G := G) g ((b j : ↥E) : Lp ℂ 2 (pwHaar G))⟫ := by
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis,
    Submodule.coe_inner, pwU_coe]

end MathlibExt.Topology.Algebra.PeterWeylWanted

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/--
[pwRep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma pwRep (E : Submodule ℂ (Lp ℂ 2 (pwHaar G)))
  (hfin : FiniteDimensional ℂ ↥E)
  (hinv : ∀ (g : G) (v : Lp ℂ 2 (pwHaar G)),
    v ∈ E → pwTransl (G := G) g v ∈ E)
  (hcont : ∀ (u v : ↥E), Continuous fun g =>
    ⟪(u : Lp ℂ 2 (pwHaar G)), pwTransl (G := G) g (v : Lp ℂ 2 (pwHaar G))⟫)
  (z : G) (v₀m : ↥E)
  (hne0 : pwTransl (G := G) z (v₀m : Lp ℂ 2 (pwHaar G))
    ≠ (v₀m : Lp ℂ 2 (pwHaar G))) :
  ∃ (n : ℕ) (_hn : 0 < n) (ρ : G → Matrix (Fin n) (Fin n) ℂ),
    Continuous ρ ∧ ρ 1 = 1 ∧ (∀ g h : G, ρ (g * h) = ρ g * ρ h) ∧
    (∀ g : G, ρ g ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧ ρ z ≠ 1 := by
  have := hfin
  set b : OrthonormalBasis (Fin (Module.finrank ℂ ↥E)) ℂ ↥E :=
    stdOrthonormalBasis ℂ ↥E with hbdef
  set ρ : G → Matrix (Fin (Module.finrank ℂ ↥E)) (Fin (Module.finrank ℂ ↥E)) ℂ :=
    fun g => LinearMap.toMatrix b.toBasis b.toBasis (pwU (G := G) E hinv g)
    with hρdef
  have hρ : ∀ g : G, ρ g
    = LinearMap.toMatrix b.toBasis b.toBasis (pwU (G := G) E hinv g) :=
    fun _ => rfl
  have hv0 : v₀m ≠ 0 := by
    intro h0
    apply hne0
    simp [h0]
  have : Nontrivial ↥E := ⟨v₀m, 0, hv0⟩
  have hn : 0 < Module.finrank ℂ ↥E := Module.finrank_pos_iff.mpr ‹Nontrivial ↥E›
  have hρcont : Continuous ρ := by
    apply continuous_matrix
    intro i j
    have e : (fun a => ρ a i j)
      = (fun g => ⟪((b i : ↥E) : Lp ℂ 2 (pwHaar G)),
        pwTransl (G := G) g ((b j : ↥E) : Lp ℂ 2 (pwHaar G))⟫) := by
      funext g
      rw [hρ]
      exact pwRep_entry E hinv b g i j
    rw [e]
    exact hcont (b i) (b j)
  have hρ1 : ρ 1 = 1 := by
    rw [hρ, pwU_one, LinearMap.toMatrix_one]
  have hρmul : ∀ g h : G, ρ (g * h) = ρ g * ρ h := by
    intro g h
    rw [hρ, hρ, hρ, pwU_mul, LinearMap.toMatrix_mul]
  have hρunit : ∀ g : G, ρ g ∈ Matrix.unitaryGroup (Fin _) ℂ := by
    intro g
    rw [Matrix.mem_unitaryGroup_iff']
    have hstar : star (ρ g) = ρ g⁻¹ := by
      apply Matrix.ext
      intro i j
      rw [hρ, hρ, Matrix.star_apply, pwRep_entry E hinv b g j i,
        ← starRingEnd_apply, inner_conj_symm, pwTransl_inner,
        ← pwRep_entry E hinv b g⁻¹ i j]
    rwa [hstar, ← hρmul, inv_mul_cancel]
  have hρne : ρ z ≠ 1 := by
    intro hcon
    have h2 : LinearMap.toMatrix b.toBasis b.toBasis (pwU (G := G) E hinv z)
      = 1 := by
      rwa [← hρ]
    have h3 : (LinearMap.toMatrix b.toBasis b.toBasis) (pwU (G := G) E hinv z)
      = (LinearMap.toMatrix b.toBasis b.toBasis) 1 := by
      rwa [LinearMap.toMatrix_one]
    have hUz : pwU (G := G) E hinv z = 1 :=
      (LinearMap.toMatrix b.toBasis b.toBasis).injective h3
    have h4 : (pwU (G := G) E hinv z) v₀m = v₀m := by
      rw [hUz]
      simp
    apply hne0
    have h5 := pwU_coe (G := G) E hinv z v₀m
    rwa [h4] at h5
  exact ⟨Module.finrank ℂ ↥E, hn, ρ, hρcont, hρ1, hρmul, hρunit, hρne⟩

end MathlibExt.Topology.Algebra.PeterWeylWanted

/--
[peter_weyl_point_separation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma peter_weyl_point_separation_eq
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  {x y : G}
-- given
  (hxy : x ≠ y) :
-- imply
  ∃ (n : ℕ) (_hn : 0 < n) (ρ : G → Matrix (Fin n) (Fin n) ℂ),
    Continuous ρ ∧
    ρ 1 = 1 ∧
    (∀ g h : G, ρ (g * h) = ρ g * ρ h) ∧
    (∀ g : G, ρ g ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
    ρ x ≠ ρ y := by
-- proof
  apply MathlibExt.Topology.Algebra.PeterWeylWanted.peter_weyl_point_separation hxy


-- created on 2026-10-20
-- updated on 2026-10-26
