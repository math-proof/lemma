import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Def.Analysis.SpecialFunctions.Trigonometric
import Syntax.Analysis.Calculus.Deriv.Operators
import Initialize.Tactic.Attr.Basic
open Real Complex


/--
Catenary from static force balance \(F=0\) (悬链线), complex form.

Discrete free-body on a cable arc of horizontal span \(\Delta x\to 0^+\):
\[
  \mathbf{T}(x+\Delta x)-\mathbf{T}(x)+\mu g\,\Delta s\,\widehat{\mathbf y}=0,
  \qquad \Delta s=\sqrt{1+(y')^2}\,\Delta x
\]
(acceleration vanishes). Tangential tension of magnitude \(T(x)\) at angle
\(\theta=\arctan y'\) is the complex amplitude \(T e^{i\theta}\). Binder
`h_force` is
\[
  \partial_x\bigl(T e^{i\theta}\bigr)=i\cdot\mu\sqrt{1+(y_x)^2}\cdot g,
\]
encoding both \(\partial_x(T\cos\theta)=0\) and
\(\partial_x(T\sin\theta)=\mu\sqrt{1+(y_x)^2}\cdot g\). The horizontal part
yields a constant \(H:=T\cos\theta\); with \(a=H/(\mu g)\) one obtains the
catenary ODE
\[
  y_{xx}=a^{-1}\sqrt{1+(y_x)^2}.
\]
-/
@[path]
private lemma main
  {μ g : ℝ⁺}
  {T y : ℝ → ℝ}
-- given
  (hT : Differentiable ℝ T)
  (hy : ContDiff ℝ 2 y)
  (h_force : ∀ x,
    ∂[x] (T x * exp (I * (∂[x] y x).arctan)) =
      I * (μ * √(1 + (∂[x] y x) ^ 2) * g)) :
-- imply
  ∃ H : ℝ,
    let a := H / (μ * g)
    ∀ x, ∂[x, x] y x = a⁻¹ * √(1 + (∂[x] y x) ^ 2) := by
-- proof
  have hμ0 : (μ : ℝ) ≠ 0 := ne_of_gt μ.property
  have hg0 : (g : ℝ) ≠ 0 := ne_of_gt g.property
  have hy1' : Differentiable ℝ (deriv y) := hy.differentiable_deriv_two
  set θ : ℝ → ℝ := fun ξ => Real.arctan (deriv y ξ)
  set U : ℝ → ℝ := fun ξ => T ξ * Real.cos (θ ξ)
  set V : ℝ → ℝ := fun ξ => T ξ * Real.sin (θ ξ)
  set W : ℝ → ℂ := fun ξ => T ξ * exp (I * θ ξ)
  have hW_eq : W = fun ξ => (U ξ : ℂ) + I * (V ξ : ℂ) := by
    funext ξ
    simp only [W, U, V, θ]
    have hExp : exp (I * Real.arctan (deriv y ξ)) =
        ↑(Real.cos (Real.arctan (deriv y ξ))) +
          ↑(Real.sin (Real.arctan (deriv y ξ))) * I := by
      rw [mul_comm I]
      apply exp_ofReal_mul_I _
    rw [hExp, mul_add, ← ofReal_mul]
    congr 1
    calc
      _ = ↑(T ξ) * ↑(Real.sin (Real.arctan (deriv y ξ))) * I := by ring
      _ = ↑(T ξ * Real.sin (Real.arctan (deriv y ξ))) * I := by rw [← ofReal_mul]
      _ = I * ↑(T ξ * Real.sin (Real.arctan (deriv y ξ))) := by rw [mul_comm]
  have hθ_diff : ContDiff ℝ 1 θ := by
    change ContDiff ℝ 1 (Real.arctan ∘ deriv y)
    exact Real.contDiff_arctan.comp hy.deriv'
  have hU_diff : Differentiable ℝ U := by
    have h_cos : ContDiff ℝ 1 (Real.cos ∘ θ) := Real.contDiff_cos.comp hθ_diff
    refine Differentiable.mul hT ?_
    change Differentiable ℝ (Real.cos ∘ θ)
    apply h_cos.differentiable_one
  have hV_diff : Differentiable ℝ V := by
    have h_sin : ContDiff ℝ 1 (Real.sin ∘ θ) := Real.contDiff_sin.comp hθ_diff
    refine Differentiable.mul hT ?_
    change Differentiable ℝ (Real.sin ∘ θ)
    apply h_sin.differentiable_one
  have hW_deriv : ∀ x, deriv W x = ↑(deriv U x) + I * ↑(deriv V x) := by
    intro x
    have hUd : HasDerivAt U (deriv U x) x := (hU_diff x).hasDerivAt
    have hVd : HasDerivAt V (deriv V x) x := (hV_diff x).hasDerivAt
    have hU' : HasDerivAt (fun ξ => (U ξ : ℂ)) ↑(deriv U x) x :=
      hUd.ofReal_comp
    have hV' : HasDerivAt (fun ξ => (V ξ : ℂ)) ↑(deriv V x) x :=
      hVd.ofReal_comp
    have hIV : HasDerivAt (fun ξ => I * (V ξ : ℂ))
        (I * ↑(deriv V x)) x :=
      hV'.const_mul I
    have hsum := hU'.add hIV
    have hfun : (fun ξ => (U ξ : ℂ)) + (fun ξ => I * (V ξ : ℂ)) =
        fun ξ => (U ξ : ℂ) + I * (V ξ : ℂ) := rfl
    simpa [hW_eq, ← hfun] using hsum.deriv
  have h_horiz : ∀ x, deriv U x = 0 := by
    intro x
    have hW0 : deriv W x =
        I * ↑(μ * √(1 + (deriv y x) ^ 2) * g) := by
      simpa [W, θ] using h_force x
    have hre := congrArg re (hW_deriv x ▸ hW0)
    -- re(↑U' + I*↑V') = U'; re(I*↑r) = 0
    simp [add_re, mul_re, I_re, I_im,
      ofReal_re, ofReal_im] at hre
    apply hre
  have h_vert : ∀ x, deriv V x =
      μ * √(1 + (deriv y x) ^ 2) * g := by
    intro x
    have hW0 : deriv W x =
        I * ↑(μ * √(1 + (deriv y x) ^ 2) * g) := by
      simpa [W, θ] using h_force x
    have him := congrArg im (hW_deriv x ▸ hW0)
    simp [add_im, mul_im, I_re, I_im,
      ofReal_re, ofReal_im] at him
    apply him
  have hU_const : ∀ x, U x = U 0 := fun x =>
    is_const_of_deriv_eq_zero hU_diff h_horiz x 0
  set H : ℝ := U 0
  have hUH : ∀ x, U x = H := by
    intro x
    simpa [H] using hU_const x
  have hH0 : H ≠ 0 := by
    intro hH
    have hV0 : ∀ ξ, V ξ = 0 := by
      intro ξ
      set u : ℝ := deriv y ξ
      have hc : T ξ * Real.cos (Real.arctan u) = 0 := by
        simpa [U, H, hH, θ, u] using hUH ξ
      have hcos_ne : Real.cos (Real.arctan u) ≠ 0 := by
        rw [Real.cos_arctan]
        refine div_ne_zero one_ne_zero ?_
        exact (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one
          (le_add_of_nonneg_right (sq_nonneg _)))).ne'
      have hT0 : T ξ = 0 := by
        apply mul_right_cancel₀ hcos_ne
        simpa using hc
      simp [V, hT0]
    have hspos : 0 < √(1 + (deriv y 0) ^ 2) :=
      Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (sq_nonneg _)))
    have hL : deriv V 0 = 0 := by
      have hfun : V = fun _ => 0 := by
        funext ξ
        exact hV0 ξ
      simp [hfun]
    refine mul_ne_zero (mul_ne_zero hμ0 hspos.ne') hg0 ?_
    simpa [hL] using (h_vert 0).symm
  refine ⟨H, ?_⟩
  intro a x
  set ux : ℝ := ∂[x] y x
  set uxx : ℝ := ∂[x, x] y x
  have h_ux_deriv : HasDerivAt (deriv y) uxx x := by
    simpa [uxx] using (hy1' x).hasDerivAt
  -- V = H·y' ⇒ ODE from vertical balance.
  have hV_eq : V = fun ξ => H * deriv y ξ := by
    funext ξ
    set u : ℝ := deriv y ξ
    have hc : T ξ * Real.cos (Real.arctan u) = H := by
      simpa [U, θ, u] using hUH ξ
    have hcos_ne : Real.cos (Real.arctan u) ≠ 0 := by
      rw [Real.cos_arctan]
      refine div_ne_zero one_ne_zero ?_
      exact (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (sq_nonneg _)))).ne'
    simp only [V]
    calc
      _ = T ξ * Real.sin (Real.arctan u) := rfl
      _ = T ξ * Real.cos (Real.arctan u) *
          (Real.sin (Real.arctan u) / Real.cos (Real.arctan u)) := by
        field_simp [hcos_ne]
      _ = H * Real.tan (Real.arctan u) := by
        rw [hc, Real.tan_eq_sin_div_cos]
      _ = H * u := by rw [Real.tan_arctan]
  have hV_derivAt : HasDerivAt V (H * uxx) x := by
    rw [hV_eq]
    apply h_ux_deriv.const_mul H
  have hforce' : H * uxx = μ * √(1 + ux ^ 2) * g := by
    simpa [ux, hV_derivAt.deriv] using h_vert x
  have hode' : uxx = a⁻¹ * √(1 + ux ^ 2) := calc
    _ = H⁻¹ * (H * uxx) := by field_simp [hH0]
    _ = H⁻¹ * (μ * √(1 + ux ^ 2) * g) := by rw [hforce']
    _ = a⁻¹ * √(1 + ux ^ 2) := by
      simp only [a]
      field_simp [hH0, hμ0, hg0]
  simpa [ux, uxx] using hode'


-- created on 2026-11-06
