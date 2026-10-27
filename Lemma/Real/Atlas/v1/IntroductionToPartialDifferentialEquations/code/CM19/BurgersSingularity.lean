import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM19.BurgersSingularity
open Finset MeasureTheory Set TransportBurgers


namespace TransportBurgers

/--
[burgers_char_zero_accel_time](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/BurgersSingularity.lean)
-/
@[path]
lemma burgers_char_zero_accel_time
  {g0 : ℝ → ℝ}
-- given
  (hg0 : ∀ s, deriv g0 s = 1) :
-- imply
  ∀ s, (deriv (deriv g0) s : ℝ) = 0 := by
-- proof
  intro s
  have : deriv g0 = fun _ => (1 : ℝ) := funext hg0
  rw [this]
  exact deriv_const s 1

end TransportBurgers

namespace TransportBurgers

/--
[burgers_char_zero_accel_space](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/BurgersSingularity.lean)
-/
@[path]
lemma burgers_char_zero_accel_space
  {u : ℝ → ℝ → ℝ}
  {g0 g1 : ℝ → ℝ}
-- given
  (hchar : IsBurgersCharacteristic u g0 g1)
  (hconst : ∀ s, deriv (fun s => u (g0 s) (g1 s)) s = 0)
  (hg1_diff : Differentiable ℝ g1) :
-- imply
  ∀ s, (deriv (deriv g1) s : ℝ) = 0 := by
-- proof
  intro s
  have hderiv_eq : deriv g1 = fun s => u (g0 s) (g1 s) := by
    ext s'
    have h1 : HasDerivAt g1 (u (g0 s') (g1 s')) s' := by
      rw [← hchar.2 s']
      exact (hg1_diff s').hasDerivAt
    exact h1.deriv
  rw [hderiv_eq]
  exact hconst s

end TransportBurgers

namespace TransportBurgers

/--
[ode_unique_zero_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/BurgersSingularity.lean)
-/
@[path]
lemma ode_unique_zero_pos
  {s : ℝ}
-- given
  (w h : ℝ → ℝ)
  (hw_diff : Differentiable ℝ w)
  (hw0 : w 0 = 0)
  (hh_cont : Continuous h)
  (hw_eq : ∀ s₀, HasDerivAt w (-w s₀ * h s₀) s₀)
  (hs : 0 ≤ s) :
-- imply
  w s = 0 := by
-- proof
  have hh_bdd : ∃ K : ℝ, ∀ t ∈ Icc 0 s, ‖h t‖ ≤ K := by
    have := (isCompact_Icc (a := 0) (b := s)).bddAbove_image hh_cont.norm.continuousOn
    obtain ⟨K, hK⟩ := this; exact ⟨K, fun t ht => hK ⟨t, ht, rfl⟩⟩
  obtain ⟨K, hK⟩ := hh_bdd
  have hws : ‖w s‖ ≤ gronwallBound 0 K 0 (s - 0) := by
    apply norm_le_gronwallBound_of_norm_deriv_right_le
      (hw_diff.continuous.continuousOn (s := Icc 0 s))
    · intro x _; exact (hw_eq x).hasDerivWithinAt
    · simp [hw0]
    · intro x hx
      calc ‖-w x * h x‖ = ‖w x‖ * ‖h x‖ := by
        rw [show -w x * h x = -(w x * h x) from by ring, norm_neg, norm_mul]
        _ ≤ ‖w x‖ * K :=
          mul_le_mul_of_nonneg_left (hK x (Ico_subset_Icc_self hx)) (norm_nonneg _)
        _ = K * ‖w x‖ + 0 := by ring
    · exact ⟨hs, le_refl s⟩
  simp [gronwallBound] at hws; exact hws

end TransportBurgers

namespace TransportBurgers

/--
[ode_unique_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/BurgersSingularity.lean)
-/
@[path]
lemma ode_unique_zero
  {s : ℝ}
-- given
  (w h : ℝ → ℝ)
  (hw_diff : Differentiable ℝ w)
  (hw0 : w 0 = 0)
  (hh_cont : Continuous h)
  (hw_eq : ∀ s₀, HasDerivAt w (-w s₀ * h s₀) s₀) :
-- imply
  w s = 0 := by
-- proof
  by_cases hs : 0 ≤ s
  · exact ode_unique_zero_pos w h hw_diff hw0 hh_cont hw_eq s hs
  · push Not at hs
    have key : w (-(-s)) = 0 :=
      ode_unique_zero_pos (fun t => w (-t)) (fun t => -h (-t))
        (hw_diff.comp differentiable_neg) (by simp [hw0])
        ((hh_cont.comp continuous_neg).neg)
        (fun t => by
          have h1 := (hw_eq (-t)).comp t (hasDerivAt_neg t)
          simp at h1; convert h1 using 1; ring)
        (-s) (by linarith)
    simpa using key

end TransportBurgers

namespace TransportBurgers

/--
[burgers_constant_along_straight_char](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/BurgersSingularity.lean)
-/
@[path]
lemma burgers_constant_along_straight_char
  {u : ℝ → ℝ → ℝ}
  {f : ℝ → ℝ}
  {p s : ℝ}
-- given
  (hu : SolvesBurgers u)
  (hu_C1 : ContDiff ℝ 1 (Function.uncurry u))
  (hdata : ∀ x, u 0 x = f x) :
-- imply
  u s (p + f p * s) = f p := by
-- proof
  set c := f p
  set U := Function.uncurry u
  set w : ℝ → ℝ := fun s₀ => u s₀ (p + c * s₀) - c
  set h_func : ℝ → ℝ := fun s₀ => deriv (fun x' => u s₀ x') (p + c * s₀)
  have hU_diff : Differentiable ℝ U := hu_C1.differentiable one_ne_zero
  have hw_diff : Differentiable ℝ w := by
    apply Differentiable.sub _ (differentiable_const c)
    intro s₀
    exact hU_diff.differentiableAt.comp s₀
      (differentiableAt_id.prodMk
        ((differentiableAt_const p).add ((differentiableAt_const c).mul differentiableAt_id)))
  have hw0 : w 0 = 0 := by simp [w, hdata p, c]
  have hh_cont : Continuous h_func := by
    have hfderiv_cont : Continuous (fderiv ℝ U) := hu_C1.continuous_fderiv one_ne_zero
    have hline_cont : Continuous (fun s₀ => (s₀, p + c * s₀)) :=
      continuous_id.prodMk (continuous_const.add (continuous_const.mul continuous_id))
    have hcomp_cont : Continuous (fun s₀ => fderiv ℝ U (s₀, p + c * s₀)) :=
      hfderiv_cont.comp hline_cont
    have heval : Continuous (fun (L : ℝ × ℝ →L[ℝ] ℝ) => L (0, 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (0, 1)).continuous
    suffices heq : h_func = fun s₀ => fderiv ℝ U (s₀, p + c * s₀) (0, 1) from
      heq ▸ heval.comp hcomp_cont
    ext s₀
    simp only [h_func]
    symm
    have hcomp : HasFDerivAt (fun x' => U (s₀, x'))
      ((fderiv ℝ U (s₀, p + c * s₀)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) (p + c * s₀) :=
      HasFDerivAt.comp (p + c * s₀) (hU_diff.differentiableAt (x := (s₀, p + c * s₀))).hasFDerivAt
        (hasFDerivAt_prodMk_right s₀ (p + c * s₀) :
          HasFDerivAt (fun x' => (s₀, x')) (ContinuousLinearMap.inr ℝ ℝ ℝ) (p + c * s₀))
    have hd := hcomp.hasDerivAt
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hd
    exact hd.deriv.symm
  have hw_eq : ∀ s₀, HasDerivAt w (-w s₀ * h_func s₀) s₀ := by
    intro s₀
    have hφ : HasDerivAt (fun s => (s, p + c * s)) ((1 : ℝ), c) s₀ :=
      (hasDerivAt_id s₀).prodMk (by simpa using (hasDerivAt_id s₀).const_mul c |>.const_add p)
    have hchain := (hU_diff.differentiableAt (x := (s₀, p + c * s₀))).hasFDerivAt.comp_hasDerivAt s₀ hφ
    have hval : fderiv ℝ U (s₀, p + c * s₀) ((1:ℝ), c) =
      deriv (fun t' => u t' (p + c * s₀)) s₀ + c * h_func s₀ := by
      have h_t : fderiv ℝ U (s₀, p + c * s₀) (1, 0) = deriv (fun t' => u t' (p + c * s₀)) s₀ := by
        have hc := HasFDerivAt.comp s₀ (hU_diff.differentiableAt (x := (s₀, p + c * s₀))).hasFDerivAt
          (hasFDerivAt_prodMk_left s₀ (p + c * s₀) :
            HasFDerivAt (fun t' => (t', p + c * s₀)) (ContinuousLinearMap.inl ℝ ℝ ℝ) s₀)
        exact hc.hasDerivAt.deriv.symm
      have h_x : fderiv ℝ U (s₀, p + c * s₀) (0, 1) = h_func s₀ := by
        have hc := HasFDerivAt.comp (p + c * s₀) (hU_diff.differentiableAt (x := (s₀, p + c * s₀))).hasFDerivAt
          (hasFDerivAt_prodMk_right s₀ (p + c * s₀) :
            HasFDerivAt (fun x' => (s₀, x')) (ContinuousLinearMap.inr ℝ ℝ ℝ) (p + c * s₀))
        exact hc.hasDerivAt.deriv.symm
      have hd : ((1:ℝ), (c:ℝ)) = (1:ℝ) • ((1:ℝ), (0:ℝ)) + c • ((0:ℝ), (1:ℝ)) := by simp
      rw [hd, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h_t, h_x, one_mul]
    have hg_hasderiv : HasDerivAt (fun s => u s (p + c * s))
      (deriv (fun t' => u t' (p + c * s₀)) s₀ + c * h_func s₀) s₀ := by
      convert hchain using 1; exact hval.symm
    have hw_hasderiv := hg_hasderiv.sub_const c
    have hburg := hu s₀ (p + c * s₀)
    have heq_val : deriv (fun t' => u t' (p + c * s₀)) s₀ + c * h_func s₀ = -w s₀ * h_func s₀ := by
      have : deriv (fun t' => u t' (p + c * s₀)) s₀ =
        -(u s₀ (p + c * s₀) * h_func s₀) := by linarith
      rw [this]; simp [w, h_func]; ring
    rwa [heq_val] at hw_hasderiv
  have hresult := ode_unique_zero w h_func hw_diff hw0 hh_cont hw_eq s
  simp [w] at hresult
  linarith

end TransportBurgers

namespace TransportBurgers

/--
[burgers_implicit_solution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/BurgersSingularity.lean)
-/
@[path]
lemma burgers_implicit_solution
  {u : ℝ → ℝ → ℝ}
  {f : ℝ → ℝ}
  {t x p : ℝ}
-- given
  (hu : SolvesBurgers u)
  (hu_C1 : ContDiff ℝ 1 (Function.uncurry u))
  (hdata : ∀ x, u 0 x = f x)
  (hp : x = p + f p * t) :
-- imply
  u t x = f p := by
-- proof
  rw [hp]
  exact burgers_constant_along_straight_char u f hu hu_C1 hdata p t

end TransportBurgers

namespace TransportBurgers

/--
[exists_gt_of_deriv_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/BurgersSingularity.lean)
-/
@[path]
lemma exists_gt_of_deriv_neg
  {f : ℝ → ℝ}
  {x₀ : ℝ}
-- given
  (hf_diff : Differentiable ℝ f)
  (hf'_neg : deriv f x₀ < 0) :
-- imply
  ∃ x₁ > x₀, f x₁ < f x₀ := by
-- proof
  have hda := (hf_diff x₀).hasDerivAt
  have hslope := hda.tendsto_slope_zero_right
  have hev : ∀ᶠ h in nhdsWithin (0:ℝ) (Ioi 0), h⁻¹ • (f (x₀ + h) - f x₀) < 0 :=
    hslope.eventually (gt_mem_nhds (by linarith : (0:ℝ) > deriv f x₀))
  have hev_pos : ∀ᶠ h in nhdsWithin (0:ℝ) (Ioi 0), (0:ℝ) < h :=
    eventually_nhdsWithin_of_forall (fun x hx => hx)
  obtain ⟨h, hh_slope, hh_pos⟩ := (hev.and hev_pos).exists
  refine ⟨x₀ + h, by linarith, ?_⟩
  have hinv_pos : (0:ℝ) < h⁻¹ := inv_pos.mpr hh_pos
  have : f (x₀ + h) - f x₀ < 0 := by
    by_contra h_ge
    push Not at h_ge
    have : (0:ℝ) ≤ h⁻¹ • (f (x₀ + h) - f x₀) :=
      smul_nonneg (le_of_lt hinv_pos) h_ge
    linarith
  linarith

end TransportBurgers

namespace TransportBurgers

/--
[singularity_forward_chars_cross](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/BurgersSingularity.lean)
-/
@[path]
lemma singularity_forward_chars_cross
  {f : ℝ → ℝ}
  {x₀ : ℝ}
-- given
  (hf_diff : Differentiable ℝ f)
  (hf'_neg : deriv f x₀ < 0) :
-- imply
  ∃ (p₀ p₁ : ℝ) (t : ℝ), p₀ ≠ p₁ ∧ 0 < t ∧ p₀ + f p₀ * t = p₁ + f p₁ * t := by
-- proof
  obtain ⟨x₁, hx₁_gt, hf_lt⟩ := exists_gt_of_deriv_neg f hf_diff x₀ hf'_neg
  refine ⟨x₀, x₁, (x₁ - x₀) / (f x₀ - f x₁), ne_of_lt hx₁_gt, ?_, ?_⟩
  ·
    exact div_pos (by linarith) (by linarith)
  ·
    have hne : f x₀ - f x₁ ≠ 0 := by linarith
    field_simp
    ring

end TransportBurgers

namespace TransportBurgers

/--
[singularity_forward_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/BurgersSingularity.lean)
-/
@[path]
lemma singularity_forward_contradiction
  {u : ℝ → ℝ → ℝ}
  {f : ℝ → ℝ}
  {x₀ : ℝ}
-- given
  (hdata : ∀ x, u 0 x = f x)
  (hconst_char : ∀ p s, u s (p + f p * s) = u 0 p)
  (hf_diff : Differentiable ℝ f)
  (hf'_neg : deriv f x₀ < 0) :
-- imply
  ∃ (p₀ p₁ : ℝ) (t : ℝ) (x : ℝ), p₀ ≠ p₁ ∧ 0 < t ∧ f p₀ ≠ f p₁ ∧ u t x = f p₀ ∧ u t x = f p₁ := by
-- proof
  obtain ⟨p₀, p₁, t, hp_ne, ht_pos, hcross⟩ :=
    singularity_forward_chars_cross f hf_diff x₀ hf'_neg
  refine ⟨p₀, p₁, t, p₀ + f p₀ * t, hp_ne, ht_pos, ?_, ?_, ?_⟩
  ·
    intro heq
    apply hp_ne
    have : p₀ + f p₀ * t = p₁ + f p₁ * t := hcross
    rw [heq] at this
    linarith
  · rw [hconst_char p₀ t, hdata p₀]
  · rw [hcross, hconst_char p₁ t, hdata p₁]

end TransportBurgers

namespace TransportBurgers

/--
[transport_equation_from_ift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/BurgersSingularity.lean)
-/
@[path]
lemma transport_equation_from_ift
  {f : ℝ → ℝ}
  {p₀ : ℝ → ℝ → ℝ}
-- given
  (hf_C1 : ContDiff ℝ 1 f)
  (hf'_nonneg : ∀ x, 0 ≤ deriv f x)
  (hp₀_rel : ∀ t x, x = p₀ t x + f (p₀ t x) * t)
  (hp₀_C1 : ContDiff ℝ 1 (Function.uncurry p₀)) :
-- imply
  ∀ t x, deriv (fun t' => p₀ t' x) t + f (p₀ t x) * deriv (fun x' => p₀ t x') x = 0 := by
-- proof
  intro t x
  set P := Function.uncurry p₀
  have hP_diff : Differentiable ℝ P := hp₀_C1.differentiable (by norm_num)
  have hf_diff : Differentiable ℝ f := hf_C1.differentiable (by norm_num)
  have hp₀_t_diff : Differentiable ℝ (fun t' => p₀ t' x) := by
    intro t'
    have : (fun t' => p₀ t' x) = P ∘ (fun t' => (t', x)) := by ext; simp [P, Function.uncurry]
    rw [this]
    exact hP_diff.differentiableAt.comp t' (differentiableAt_id.prodMk (differentiableAt_const _))
  have hp₀_x_diff : Differentiable ℝ (fun x' => p₀ t x') := by
    intro x'
    have : (fun x' => p₀ t x') = P ∘ (fun x' => (t, x')) := by ext; simp [P, Function.uncurry]
    rw [this]
    exact hP_diff.differentiableAt.comp x' ((differentiableAt_const _).prodMk differentiableAt_id)
  have hfp₀_t_diff : Differentiable ℝ (fun t' => f (p₀ t' x)) := hf_diff.comp hp₀_t_diff
  have hfp₀_x_diff : Differentiable ℝ (fun x' => f (p₀ t x')) := hf_diff.comp hp₀_x_diff
  have h_Phi_t : deriv (fun t' => p₀ t' x + f (p₀ t' x) * t') t = 0 := by
    have : (fun t' => p₀ t' x + f (p₀ t' x) * t') = fun _ => x := by
      ext t'; linarith [hp₀_rel t' x]
    rw [this, deriv_const]
  have h_Phi_x : deriv (fun x' => p₀ t x' + f (p₀ t x') * t) x = 1 := by
    have : (fun x' => p₀ t x' + f (p₀ t x') * t) = id := by
      ext x'; simp [id]; linarith [hp₀_rel t x']
    rw [this, deriv_id']
  have h_expand_t : deriv (fun t' => p₀ t' x + f (p₀ t' x) * t') t =
    deriv (fun t' => p₀ t' x) t +
    (deriv (fun t' => f (p₀ t' x)) t * t + f (p₀ t x)) := by
    have h1 : HasDerivAt (fun t' => p₀ t' x) (deriv (fun t' => p₀ t' x) t) t :=
      (hp₀_t_diff t).hasDerivAt
    have h2 : HasDerivAt (fun t' => f (p₀ t' x)) (deriv (fun t' => f (p₀ t' x)) t) t :=
      (hfp₀_t_diff t).hasDerivAt
    have h3 : HasDerivAt (fun t' => f (p₀ t' x) * t')
      (deriv (fun t' => f (p₀ t' x)) t * t + f (p₀ t x) * 1) t :=
      h2.mul (hasDerivAt_id t)
    simp only [mul_one] at h3
    exact (h1.add h3).deriv
  have h_chain_t : deriv (fun t' => f (p₀ t' x)) t =
    deriv f (p₀ t x) * deriv (fun t' => p₀ t' x) t :=
    ((hf_diff (p₀ t x)).hasDerivAt.comp t (hp₀_t_diff t).hasDerivAt).deriv
  have h_expand_x : deriv (fun x' => p₀ t x' + f (p₀ t x') * t) x =
    deriv (fun x' => p₀ t x') x + deriv (fun x' => f (p₀ t x')) x * t :=
    ((hp₀_x_diff x).hasDerivAt.add ((hfp₀_x_diff x).hasDerivAt.mul_const t)).deriv
  have h_chain_x : deriv (fun x' => f (p₀ t x')) x =
    deriv f (p₀ t x) * deriv (fun x' => p₀ t x') x :=
    ((hf_diff (p₀ t x)).hasDerivAt.comp x (hp₀_x_diff x).hasDerivAt).deriv
  set A := deriv (fun t' => p₀ t' x) t
  set B := deriv (fun x' => p₀ t x') x
  set c := f (p₀ t x)
  set d := deriv f (p₀ t x)
  have eq1 : A + d * A * t + c = 0 := by
    have := h_Phi_t; rw [h_expand_t, h_chain_t] at this; linarith
  have eq2 : B + d * B * t = 1 := by
    have := h_Phi_x; rw [h_expand_x, h_chain_x] at this; linarith
  have h_nonzero : 1 + d * t ≠ 0 := by
    intro h
    have hB : B * (1 + d * t) = 1 := by linarith [eq2]
    rw [h, mul_zero] at hB; exact zero_ne_one hB
  have h_factor : (A + c * B) * (1 + d * t) = 0 := by
    have : (A + c * B) * (1 + d * t) = A + d * A * t + c * (B + d * B * t) := by ring
    rw [this, eq2]; linarith
  exact (mul_eq_zero.mp h_factor).resolve_right h_nonzero
/-- Combined IFT-with-transport statement: if $f \in C^1$ with $f' \ge 0$, then
the characteristic inverse $p_0$ exists, is $C^1$, agrees with the identity at
$t = 0$, satisfies $x = p_0 + f(p_0) t$, and obeys the transport PDE
$\partial_t p_0 + f(p_0) \partial_x p_0 = 0$. -/

end TransportBurgers


-- created on 2026-10-23
