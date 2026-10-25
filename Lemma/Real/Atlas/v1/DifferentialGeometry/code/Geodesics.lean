import Mathlib
import sympy.Basic
import Class.v1.Atlas.DifferentialGeometry.code.Geodesics
open MeasureTheory intervalIntegral Hypersurface Finset Geodesics
open scoped InnerProductSpace BigOperators


namespace Geodesics

/--
[deriv_mem_tangentSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Geodesics.lean)
-/
@[path]
lemma deriv_mem_tangentSpace
  {n : ℕ}
  {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
  {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
  {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
  {t : ℝ}
-- given
  (hsmooth : ContDiff ℝ ⊤ γ)
  (hM : ∀ t, γ t ∈ M)
  (hψ : IsLocalDefiningFunction ψ M (γ t)) :
-- imply
  deriv γ t ∈ Hypersurface.tangentSpace ψ (γ t) := by
-- proof
  rw [mem_tangentSpace_iff]
  obtain ⟨U, hUo, hγtU, _, hψM⟩ := hψ.exists_open_nhd
  have hγcont : Continuous γ := hsmooth.continuous
  have hPreOpen : IsOpen (γ ⁻¹' U) := hγcont.isOpen_preimage U hUo
  have htInPre : t ∈ γ ⁻¹' U := hγtU
  have hconst : ∀ᶠ s in nhds t, ψ (γ s) = 0 :=
    hPreOpen.eventually_mem htInPre |>.mono fun s hs => (hψM (γ s) hs).mp (hM s)
  have hderivComp : deriv (fun s => ψ (γ s)) t = 0 := by
    have : (fun s => ψ (γ s)) =ᶠ[nhds t] (fun _ => (0 : ℝ)) :=
      hconst.mono (fun s hs => by simp [hs])
    rw [Filter.EventuallyEq.deriv_eq this]
    simp
  have hγDiff : DifferentiableAt ℝ γ t :=
    (hsmooth.differentiable (by simp)).differentiableAt
  have hψDiff : DifferentiableAt ℝ ψ (γ t) := hψ.differentiableAt
  have hchain : HasDerivAt (fun s => ψ (γ s)) (fderiv ℝ ψ (γ t) (deriv γ t)) t :=
    (hψDiff.hasFDerivAt).comp_hasDerivAt t (hγDiff.hasDerivAt)
  linarith [hchain.deriv]

end Geodesics

namespace Geodesics

/--
[geodesic_constant_speed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Geodesics.lean)
-/
@[path]
lemma geodesic_constant_speed
  {n : ℕ}
  {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
  {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
-- given
  (hHyp : IsHypersurface M)
  (hγ : IsGeodesic M hHyp γ) :
-- imply
  ∃ c : ℝ, ∀ t, ‖deriv γ t‖ = c := by
-- proof
  obtain ⟨hsmooth, hM, hperp⟩ := hγ
  have h_inner_zero : ∀ t, ⟪deriv (deriv γ) t, deriv γ t⟫_ℝ = 0 := by
    intro t
    obtain ⟨ψ, hψ⟩ := hHyp (γ t) (hM t)
    exact hperp t ψ hψ (deriv γ t) (deriv_mem_tangentSpace hsmooth hM hψ)
  have hγ2 : ContDiff ℝ 2 γ := hsmooth.of_le le_top
  have hderiv_diff : Differentiable ℝ (deriv γ) := hγ2.differentiable_deriv_two
  have hderiv_diffAt : ∀ t, DifferentiableAt ℝ (deriv γ) t :=
    fun t => hderiv_diff.differentiableAt
  have h_norm_sq_deriv : ∀ t, deriv (fun t => ⟪deriv γ t, deriv γ t⟫_ℝ) t = 0 := by
    intro t
    rw [deriv_inner_apply ℝ (hderiv_diffAt t) (hderiv_diffAt t)]
    have h1 := real_inner_comm (deriv γ t) (deriv (deriv γ) t)
    linarith [h_inner_zero t]
  have h_norm_sq_diff : Differentiable ℝ (fun t => ⟪deriv γ t, deriv γ t⟫_ℝ) :=
    fun t => (hderiv_diffAt t).inner ℝ (hderiv_diffAt t)
  have h_norm_sq_const : ∀ s t, ⟪deriv γ s, deriv γ s⟫_ℝ = ⟪deriv γ t, deriv γ t⟫_ℝ :=
    is_const_of_deriv_eq_zero h_norm_sq_diff h_norm_sq_deriv
  have h_norm_const : ∀ s t, ‖deriv γ s‖ = ‖deriv γ t‖ := by
    intro s t
    have hsq : ‖deriv γ s‖ ^ 2 = ‖deriv γ t‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      exact h_norm_sq_const s t
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  exact ⟨‖deriv γ 0‖, fun t => h_norm_const t 0⟩

end Geodesics

namespace Geodesics

/--
[variationField_mem_tangentSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Geodesics.lean)
-/
@[path]
lemma variationField_mem_tangentSpace
  {n : ℕ}
  {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
  {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
  {a b : ℝ}
  {V : SmoothVariation M γ a b}
  {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
  {t : ℝ}
-- given
  (hψ : IsLocalDefiningFunction ψ M (γ t)) :
-- imply
  variationField V t ∈ Hypersurface.tangentSpace ψ (γ t) := by
-- proof
  rw [mem_tangentSpace_iff]
  obtain ⟨U, hUo, hγtU, _, hψM⟩ := hψ.exists_open_nhd
  have hΓcont : Continuous (fun s => V.Γ s t) := by
    have : (fun s => V.Γ s t) = (fun p : ℝ × ℝ => V.Γ p.1 p.2) ∘ (fun s => (s, t)) := by
      ext s; simp
    rw [this]
    exact V.smooth.continuous.comp (Continuous.prodMk_left t)
  have hbase : V.Γ 0 t ∈ U := by rw [V.base t]; exact hγtU
  have hPreOpen : IsOpen ((fun s => V.Γ s t) ⁻¹' U) := hΓcont.isOpen_preimage U hUo
  have h0InPre : (0 : ℝ) ∈ (fun s => V.Γ s t) ⁻¹' U := hbase
  have hconst : ∀ᶠ s in nhds (0 : ℝ), ψ (V.Γ s t) = 0 :=
    hPreOpen.eventually_mem h0InPre |>.mono fun s hs => (hψM (V.Γ s t) hs).mp (V.maps_to s t)
  have hderivComp : deriv (fun s => ψ (V.Γ s t)) 0 = 0 := by
    have : (fun s => ψ (V.Γ s t)) =ᶠ[nhds 0] (fun _ => (0 : ℝ)) :=
      hconst.mono (fun s hs => by simp [hs])
    rw [Filter.EventuallyEq.deriv_eq this]
    simp
  have hΓDiff : DifferentiableAt ℝ (fun s => V.Γ s t) 0 := by
    have : (fun s => V.Γ s t) = (fun p : ℝ × ℝ => V.Γ p.1 p.2) ∘ (fun s => (s, t)) := by
      ext s; simp
    rw [this]
    exact (V.smooth.differentiable (by simp)).differentiableAt.comp _
      (Differentiable.prodMk differentiable_id (differentiable_const t)).differentiableAt
  have hψDiff : DifferentiableAt ℝ ψ (V.Γ 0 t) := by
    rw [V.base t]; exact hψ.differentiableAt
  have hchain : HasDerivAt (fun s => ψ (V.Γ s t))
    (fderiv ℝ ψ (V.Γ 0 t) (deriv (fun s => V.Γ s t) 0)) 0 :=
    (hψDiff.hasFDerivAt).comp_hasDerivAt 0 (hΓDiff.hasDerivAt)
  have := hchain.deriv
  rw [V.base t] at this
  change fderiv ℝ ψ (γ t) (variationField V t) = 0
  change deriv (fun s => ψ (V.Γ s t)) 0 = (fderiv ℝ ψ (γ t)) (variationField V t) at this
  linarith [hderivComp, this]

end Geodesics

namespace Geodesics

/--
[metric_christoffel_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Geodesics.lean)
-/
@[path]
lemma metric_christoffel_identity
  {n : ℕ}
  {patch : HypersurfacePatch n}
  {x : Fin n → ℝ}
  {i j s : Fin n}
-- given
  (hx : x ∈ patch.domain) :
-- imply
  ∑ k : Fin n, firstFundamentalForm patch x s k * ChristoffelSymbols.christoffelSymbol patch x i j k = (ChristoffelSymbols.secondPartialDeriv patch x i j) ⬝ᵥ (patch.partialDeriv x s) := by
-- proof
  have hG := firstFundamentalForm_posDef patch x hx
  have hdet : IsUnit (firstFundamentalForm patch x).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  let v : Fin n → ℝ := fun l =>
    (ChristoffelSymbols.secondPartialDeriv patch x i j) ⬝ᵥ (patch.partialDeriv x l)
  have hcancel : (firstFundamentalForm patch x).mulVec
    ((firstFundamentalForm patch x)⁻¹.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  simp only [ChristoffelSymbols.christoffelSymbol, Matrix.mulVec, dotProduct]
  change (∑ x_1, firstFundamentalForm patch x s x_1 *
    ∑ x_2, (firstFundamentalForm patch x)⁻¹ x_1 x_2 * v x_2) = v s
  have := congr_fun hcancel s
  simp only [Matrix.mulVec, dotProduct] at this
  exact this

end Geodesics

namespace Geodesics

/--
[pathLength_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Geodesics.lean)
-/
@[path]
lemma pathLength_reverse
  {n : ℕ}
  {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
  {p q : EuclideanSpace ℝ (Fin (n + 1))}
  {γ : SmoothPathIn M p q} :
-- imply
  pathLength (reversePath γ) = pathLength γ := by
-- proof
  simp only [pathLength, reversePath]
  have hd : ∀ t, deriv (fun t => γ.toFun (1 - t)) t = -(deriv γ.toFun (1 - t)) := by
    intro t
    have hda : DifferentiableAt ℝ γ.toFun (1 - t) :=
      ((γ.smooth 1).differentiable (by simp)).differentiableAt
    have hd1 : HasDerivAt (fun t => (1 : ℝ) - t) (-1) t := by
      have := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
      simp at this
      exact this
    have hcomp := hda.hasDerivAt.scomp t hd1
    have heq : (fun t => γ.toFun (1 - t)) = γ.toFun ∘ HSub.hSub 1 := rfl
    rw [heq, hcomp.deriv]
    simp
  simp_rw [hd, norm_neg]
  rw [intervalIntegral.integral_comp_sub_left (fun t => ‖deriv γ.toFun t‖) 1]
  simp

end Geodesics

namespace Geodesics

/--
[geodesicDist_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Geodesics.lean)
-/
@[path]
lemma geodesicDist_self
  {n : ℕ}
  {M : ConnectedHypersurfaceWithPaths n}
  {p : EuclideanSpace ℝ (Fin (n + 1))}
-- given
  (hp : p ∈ M.carrier) :
-- imply
  geodesicDist M.carrier p p = 0 := by
-- proof
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, fun l ⟨γ, hγ⟩ => hγ ▸
      intervalIntegral.integral_nonneg (by norm_num) (fun t _ => norm_nonneg _)⟩
    · exact ⟨⟨fun _ => p, fun _ => contDiff_const, rfl, rfl, fun _ => hp⟩, by
      simp [pathLength, deriv_const]⟩
  · apply le_csInf
    · exact ⟨_, ⟨fun _ => p, fun _ => contDiff_const, rfl, rfl, fun _ => hp⟩, rfl⟩
    · intro l ⟨γ, hγ⟩
      rw [← hγ]
      exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ => norm_nonneg _)

end Geodesics

namespace Geodesics

/--
[geodesicDist_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Geodesics.lean)
-/
@[path]
lemma geodesicDist_comm
  {n : ℕ}
  {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
  {p q : EuclideanSpace ℝ (Fin (n + 1))} :
-- imply
  geodesicDist M p q = geodesicDist M q p := by
-- proof
  simp only [geodesicDist]
  congr 1
  ext l
  simp only [Set.mem_setOf_eq]
  exact ⟨fun ⟨γ, hγ⟩ => ⟨reversePath γ, by rw [pathLength_reverse, hγ]⟩,
    fun ⟨γ, hγ⟩ => ⟨reversePath γ, by rw [pathLength_reverse, hγ]⟩⟩

end Geodesics

namespace Geodesics

/--
[geodesicDist_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Geodesics.lean)
-/
@[path]
lemma geodesicDist_eq_zero_iff
  {n : ℕ}
  {M : ConnectedHypersurfaceWithPaths n}
  {p q : EuclideanSpace ℝ (Fin (n + 1))}
-- given
  (hp : p ∈ M.carrier)
  (hq : q ∈ M.carrier)
  (heq : geodesicDist M.carrier p q = 0) :
-- imply
  p = q := by
-- proof
  by_contra hne
  have hpos : 0 < ‖q - p‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr (Ne.symm hne)
  have hle : ‖q - p‖ ≤ geodesicDist M.carrier p q := by
    apply le_csInf
    · exact ⟨pathLength (M.pathConnected p q hp hq).some, (M.pathConnected p q hp hq).some, rfl⟩
    · intro l ⟨γ, hγ⟩
      rw [← hγ]
      have hdiff : ∀ x ∈ Set.uIcc (0 : ℝ) 1, DifferentiableAt ℝ γ.toFun x :=
        fun x _ => ((γ.smooth 1).differentiable (by simp)).differentiableAt
      have hint : IntervalIntegrable (deriv γ.toFun) volume 0 1 :=
        ((γ.smooth 1).continuous_deriv (by simp)).continuousOn.intervalIntegrable
      have hftc : ∫ t in (0 : ℝ)..1, deriv γ.toFun t = γ.toFun 1 - γ.toFun 0 :=
        integral_deriv_eq_sub hdiff hint
      calc ‖q - p‖ = ‖γ.toFun 1 - γ.toFun 0‖ := by rw [γ.target, γ.source]
        _ = ‖∫ t in (0 : ℝ)..1, deriv γ.toFun t‖ := by rw [hftc]
        _ ≤ ∫ t in (0 : ℝ)..1, ‖deriv γ.toFun t‖ := norm_integral_le_integral_norm (by norm_num)
  linarith

end Geodesics

namespace Geodesics

/--
[busemann_unique_geodesic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Geodesics.lean)
-/
@[path]
lemma busemann_unique_geodesic
  [MetricSpace X]
  [IsBusemannSpace X]
  {p q : X} :
-- imply
  (∃ γ : ℝ → X, IsMetricGeodesic γ 0 (dist p q) ∧ γ 0 = p ∧ γ (dist p q) = q) ∧ (∀ γ₁ γ₂ : ℝ → X, IsMetricGeodesic γ₁ 0 (dist p q) → γ₁ 0 = p → γ₁ (dist p q) = q → IsMetricGeodesic γ₂ 0 (dist p q) → γ₂ 0 = p → γ₂ (dist p q) = q → ∀ t ∈ Set.Icc 0 (dist p q), γ₁ t = γ₂ t) := by
-- proof
  constructor
  ·
    exact IsBusemannSpace.isGeodesicSpace p q
  ·
    intro γ₁ γ₂ hγ₁ hγ₁p hγ₁q hγ₂ hγ₂p hγ₂q t ht
    by_cases hpq : dist p q = 0
    ·
      have ht0 : t = 0 := le_antisymm (by linarith [ht.2, hpq.symm ▸ ht.2]) ht.1
      rw [ht0, hγ₁p, hγ₂p]
    ·
      have hd_pos : 0 < dist p q := by positivity
      have h_bus := IsBusemannSpace.busemann_inequality (dist p q) hd_pos
        γ₁ γ₂ hγ₁ hγ₂ (by rw [hγ₁p, hγ₂p]) t ht
      rw [hγ₁q, hγ₂q, dist_self, mul_zero] at h_bus
      exact dist_le_zero.mp h_bus

end Geodesics


-- created on 2026-10-23
