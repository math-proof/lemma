import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lemma.Real.All_EqDiv_Pow_Div3'2Mul_Deriv.of.All_EqMul_Deriv_SinArctan.All_DifferentiableAt_Deriv
import Lemma.Real.CosAdd.eq.SubCosCos_SinSin
import Syntax.Analysis.Calculus.Deriv.Operators
open Real Hyperreal


/--
[Mersenne's laws](https://en.wikipedia.org/wiki/Mersenne's_laws) for an ideal vibrating string.

Assume a separated Dirichlet mode on a string of length \(L : \mathbb{R}^+\) in
amplitude–phase form
\[
  u(t,x)=A\sin\frac{n\pi x}{L}\cos(2\pi f t+\theta)
\]
(so \(X(x)=\sin(n\pi x/L)\), \(T(t)=A\cos(2\pi f t+\theta)\), with
\(X''=-k^2 X\), \(k=n\pi/L\), and \(T''=-\omega^2 T\), \(\omega=2\pi f\)),
together with the continuum soft-string force balance `h_force`
\[
  T\,\partial_x\bigl(\sin(\arctan u_x)\bigr)=\mu\,u_{tt}
\]
(the older discrete free-body form was
\(
T(\sin(\arctan u_x(x+\Delta x))-\sin(\arctan u_x(x)))=\mu\,\Delta x\,u_{tt}
\)
for infinitesimal \(\Delta x\to 0^+\)).

Derivation:
1. From continuum `h_force` and spatial \(C^2\) regularity of the mode, apply
   [nonlinear continuum wave law from soft-string \(F=ma\)](?module=Real.All_EqDiv_Pow_Div3'2Mul_Deriv.of.All_EqMul_Deriv_SinArctan.All_DifferentiableAt_Deriv)
   to get
   \(T\,u_{xx}/(1+u_x^2)^{3/2}=\mu\,u_{tt}\).
2. At a spatial node of \(X'\) (so \(u_x=0\)) this reduces to the linear law
   \(T\,u_{xx}=\mu\,u_{tt}\); mode algebra with \(u\neq 0\) forces
   \(\omega^2=(T/\mu)\,k^2\).
3. Solve the positive root for
\[
  f=\frac{n}{2L}\sqrt{\frac{T}{\mu}}.
\]
-/
@[path]
private lemma main
  [NeZero (n : ℕ)]
  {L T μ f A : ℝ⁺}
  {θ : ℝ}
  {u : ℝ → ℝ → ℝ}
-- given
  (h_motion : ∀ t x, u t x =
    A * Real.sin (n * π * x / L) *
      Real.cos (2 * π * f * t + θ))
  (h_force : ∀ (t x : ℝ),
    T * ∂[x] (∂[x] u t x).arctan.sin = μ * ∂[t, t] u t x) :
-- imply
  f = (n : ℝ) / (2 * L) * √((T : ℝ) / μ) := by
-- proof
  set k : ℝ := n * π / L
  set angFreq : ℝ := 2 * π * f
  set X : ℝ → ℝ := fun x => Real.sin (n * π * x / L)
  set a : ℝ := A * Real.cos θ
  set b : ℝ := -A * Real.sin θ
  have hphase : ∀ t, A * Real.cos (angFreq * t + θ) =
      a * Real.cos (angFreq * t) + b * Real.sin (angFreq * t) := by
    intro t
    simp only [a, b]
    rw [CosAdd.eq.SubCosCos_SinSin]
    ring
  set Tempo : ℝ → ℝ := fun t => a * Real.cos (angFreq * t) + b * Real.sin (angFreq * t)
  have h_sep : ∀ t x, u t x = X x * Tempo t := by
    intro t x
    calc
      _ = A * Real.sin (n * π * x / L) * Real.cos (angFreq * t + θ) := by
        simpa [angFreq] using h_motion t x
      _ = X x * (A * Real.cos (angFreq * t + θ)) := by
        simp only [X]; ring
      _ = X x * Tempo t := by rw [hphase t]
  have hkS : ∀ x, X x = Real.sin (k * x) := by
    intro x
    simp only [X, k]
    congr 1
    ring
  have hS_deriv : deriv X = fun x => k * Real.cos (k * x) := by
    ext x
    have hEq : X = fun x => Real.sin (k * x) := funext hkS
    apply HasDerivAt.deriv
    rw [hEq]
    apply ((hasDerivAt_sin (k * x)).comp x _).congr_deriv
    ·
      ring_nf
    ·
      simpa using (hasDerivAt_id x).const_mul k
  have h_X' : ∀ x, HasDerivAt X (deriv X x) x := by
    intro x
    have hEq : X = fun x => Real.sin (k * x) := funext hkS
    rw [hS_deriv, hEq]
    apply ((hasDerivAt_sin (k * x)).comp x _).congr_deriv
    ·
      ring_nf
    ·
      simpa using (hasDerivAt_id x).const_mul k
  have h_X2 : ∀ x, HasDerivAt (deriv X) (-k ^ 2 * X x) x := by
    intro x
    rw [hS_deriv]
    apply (((hasDerivAt_cos (k * x)).comp x _).const_mul k).congr_deriv
    ·
      rw [hkS x]
      ring_nf
    ·
      simpa using (hasDerivAt_id x).const_mul k
  have hT_deriv : deriv Tempo =
    fun t => -a * angFreq * Real.sin (angFreq * t) + b * angFreq * Real.cos (angFreq * t) := by
    ext t
    have hlin : HasDerivAt (fun t => angFreq * t) angFreq t := by
      simpa using (hasDerivAt_id t).const_mul angFreq
    apply HasDerivAt.deriv
    apply ((((hasDerivAt_cos (angFreq * t)).comp t hlin).const_mul a).add
      (((hasDerivAt_sin (angFreq * t)).comp t hlin).const_mul b)).congr_deriv (by ring)
  have h_Tempo' : ∀ t, HasDerivAt Tempo (deriv Tempo t) t := by
    intro t
    have hlin : HasDerivAt (fun t => angFreq * t) angFreq t := by
      simpa using (hasDerivAt_id t).const_mul angFreq
    rw [hT_deriv]
    apply ((((hasDerivAt_cos (angFreq * t)).comp t hlin).const_mul a).add
      (((hasDerivAt_sin (angFreq * t)).comp t hlin).const_mul b)).congr_deriv (by ring)
  have h_Tempo2 : ∀ t, HasDerivAt (deriv Tempo) (-angFreq ^ 2 * Tempo t) t := by
    intro t
    rw [hT_deriv]
    have hlin : HasDerivAt (fun t => angFreq * t) angFreq t := by
      simpa using (hasDerivAt_id t).const_mul angFreq
    apply ((((hasDerivAt_sin (angFreq * t)).comp t hlin).const_mul (-a * angFreq)).add
      (((hasDerivAt_cos (angFreq * t)).comp t hlin).const_mul (b * angFreq))).congr_deriv
      (by simp only [Tempo]; ring)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hk : k ≠ 0 := by
    simp only [k]
    apply div_ne_zero (mul_ne_zero hn pi_ne_zero) L.property.ne'
  set x0 : ℝ := L / (2 * n)
  have h_node : ∃ x0, deriv X x0 = 0 ∧ X x0 ≠ 0 := by
    refine ⟨x0, ?_, ?_⟩
    ·
      have hcos : Real.cos (k * x0) = 0 := by
        have : k * x0 = π / 2 := by
          simp only [k, x0]
          field_simp [L.property.ne', hn]
        simp [this]
      rw [hS_deriv]
      dsimp only
      rw [hcos, mul_zero]
    ·
      have harg : n * π * x0 / L = π / 2 := by
        simp only [x0]
        field_simp [L.property.ne', hn]
      simp only [X, harg, sin_pi_div_two]
      norm_num
  have h_Tempo_ne : ∃ t0, Tempo t0 ≠ 0 := by
    refine ⟨-θ / angFreq, ?_⟩
    have hf : (f : ℝ) ≠ 0 := f.property.ne'
    have hAng : angFreq ≠ 0 := by
      simp only [angFreq]
      apply mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hf
    have hAngT : angFreq * (-θ / angFreq) = -θ := by
      field_simp [hAng]
    have hsum : A * Real.cos θ * Real.cos θ + -A * Real.sin θ * -Real.sin θ = A := calc
      _ = A * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = A * 1 := by rw [cos_sq_add_sin_sq]
      _ = (A : ℝ) := by ring
    simp only [Tempo, hAngT, a, b, cos_neg, sin_neg]
    exact hsum.symm ▸ A.property.ne'
  -- Mode product derivatives and continuum nonlinear law.
  have hX2_eq : ∀ x, ∂[x, x] X x = -k ^ 2 * X x := fun x => (h_X2 x).deriv
  have hTempo2_eq : ∀ t, ∂[t, t] Tempo t = -angFreq ^ 2 * Tempo t := fun t => (h_Tempo2 t).deriv
  have hX_diff : Differentiable ℝ X := fun x => (h_X' x).differentiableAt
  have hX'_diff : Differentiable ℝ (deriv X) := fun x => (h_X2 x).differentiableAt
  have hTempo_diff : Differentiable ℝ Tempo := fun t => (h_Tempo' t).differentiableAt
  have hTempo'_diff : Differentiable ℝ (deriv Tempo) := fun t => (h_Tempo2 t).differentiableAt
  have hutt : ∀ t x, ∂[t, t] u t x = X x * ∂[t, t] Tempo t := by
    intro t x
    have h1 : (fun t'' => u t'' x) = fun t'' => X x * Tempo t'' := by
      funext t''
      apply h_sep t'' x
    have hderiv1 : deriv (fun t'' => u t'' x) = fun t'' => X x * deriv Tempo t'' := by
      rw [h1]
      funext t''
      apply deriv_const_mul (X x) (hTempo_diff t'')
    have h2 : (fun t' => deriv (fun t'' => u t'' x) t') =
        fun t' => X x * deriv Tempo t' := by
      funext t'
      rw [hderiv1]
    change deriv (fun t' => deriv (fun t'' => u t'' x) t') t =
      X x * deriv (deriv Tempo) t
    rw [h2]
    apply deriv_const_mul (X x) (hTempo'_diff t)
  have huxx : ∀ t x, ∂[x, x] u t x = Tempo t * ∂[x, x] X x := by
    intro t x
    have h1 : (fun x'' => u t x'') = fun x'' => Tempo t * X x'' := by
      funext x''
      rw [h_sep t x'', mul_comm]
    have hderiv1 : deriv (fun x'' => u t x'') = fun x'' => Tempo t * deriv X x'' := by
      rw [h1]
      funext x''
      apply deriv_const_mul (Tempo t) (hX_diff x'')
    have h2 : (fun x' => deriv (fun x'' => u t x'') x') =
        fun x' => Tempo t * deriv X x' := by
      funext x'
      rw [hderiv1]
    change deriv (fun x' => deriv (fun x'' => u t x'') x') x =
      Tempo t * deriv (deriv X) x
    rw [h2]
    apply deriv_const_mul (Tempo t) (hX'_diff x)
  have h_ux' : ∀ t x, DifferentiableAt ℝ (deriv (u t)) x := by
    intro t x
    have h1 : (fun y => u t y) = fun y => Tempo t * X y := by
      funext y
      rw [h_sep t y, mul_comm]
    have hderiv1 : deriv (u t) = fun y => Tempo t * deriv X y := by
      have : deriv (u t) = deriv (fun y => u t y) := rfl
      rw [this, h1]
      funext y
      apply deriv_const_mul (Tempo t) (hX_diff y)
    have h2 : HasDerivAt (fun y => Tempo t * deriv X y)
        (Tempo t * (-k ^ 2 * X x)) x :=
      (h_X2 x).const_mul (Tempo t)
    simpa [hderiv1] using h2.differentiableAt
  have h_nl :
    ∀ t x,
      (T : ℝ) * (∂[x, x] u t x) / (1 + (∂[x] u t x) ^ 2) ^ ((3 : ℝ) / 2) =
        (μ : ℝ) * ∂[t, t] u t x :=
    All_EqDiv_Pow_Div3'2Mul_Deriv.of.All_EqMul_Deriv_SinArctan.All_DifferentiableAt_Deriv
      h_ux' h_force
  have huxx_mode : ∀ t x, ∂[x, x] u t x = -k ^ 2 * u t x := by
    intro t x
    rw [huxx t x, hX2_eq x, h_sep t x]
    ring
  have hutt_mode : ∀ t x, ∂[t, t] u t x = -angFreq ^ 2 * u t x := by
    intro t x
    rw [hutt t x, hTempo2_eq t, h_sep t x]
    ring
  obtain ⟨x0, hx0', hx0X⟩ := h_node
  obtain ⟨t0, ht0⟩ := h_Tempo_ne
  -- At the spatial node, u_x = 0 so the nonlinear law linearizes.
  have hux0 : deriv (u t0) x0 = 0 := by
    have h1 : (fun y => u t0 y) = fun y => Tempo t0 * X y := by
      funext y
      rw [h_sep t0 y, mul_comm]
    have hderiv1 : deriv (fun y => u t0 y) = fun y => Tempo t0 * deriv X y := by
      rw [h1]
      funext y
      apply deriv_const_mul (Tempo t0) (hX_diff y)
    have : deriv (u t0) x0 = Tempo t0 * deriv X x0 := by
      simpa using congrArg (fun f => f x0) hderiv1
    rw [this, hx0', mul_zero]
  have hpde_sample :
    (T : ℝ) * deriv (deriv (u t0)) x0 =
      (μ : ℝ) * deriv (deriv (fun t => u t x0)) t0 := by
    have hnl := h_nl t0 x0
    simp only [hux0, pow_two, mul_zero, add_zero, Real.one_rpow, div_one] at hnl
    exact hnl
  -- Recover angFreq² = (T/μ) k² from linearized sample + mode.
  have hfreq_sq : angFreq ^ 2 = (T : ℝ) / (μ : ℝ) * k ^ 2 := by
    have hp := hpde_sample
    rw [huxx_mode t0 x0, hutt_mode t0 x0] at hp
    have hμ : (μ : ℝ) ≠ 0 := μ.property.ne'
    have hu : u t0 x0 ≠ 0 := by
      rw [h_sep t0 x0]
      exact mul_ne_zero hx0X ht0
    have hmul : ((T : ℝ) * k ^ 2 - μ * angFreq ^ 2) * u t0 x0 = 0 := by
      linear_combination -hp
    have hcoef : (T : ℝ) * k ^ 2 = μ * angFreq ^ 2 := by
      have h0 : (T : ℝ) * k ^ 2 - μ * angFreq ^ 2 = 0 :=
        (mul_eq_zero.mp hmul).resolve_right hu
      linarith
    field_simp [hμ]
    linarith
  -- Solve for positive f.
  have hπ : π ≠ 0 := pi_ne_zero
  have hTμ : 0 < (T : ℝ) / (μ : ℝ) := div_pos T.property μ.property
  have hL' : (L : ℝ) ≠ 0 := L.property.ne'
  have h2π : (2 : ℝ) * π ≠ 0 := mul_ne_zero two_ne_zero hπ
  have hside : 2 * π * (f : ℝ) =
    (n : ℝ) * π / (L : ℝ) * √((T : ℝ) / (μ : ℝ)) := by
    have hnonneg_left : 0 ≤ 2 * π * (f : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) pi_pos.le)
        f.property.le
    refine (sq_eq_sq₀ hnonneg_left ?_).mp ?_
    ·
      apply mul_nonneg
      · apply div_nonneg (mul_nonneg (Nat.cast_nonneg _) pi_pos.le) L.property.le
      · apply sqrt_nonneg _
    ·
      calc
        _ = angFreq ^ 2 := by simp only [angFreq]
        _ = (T : ℝ) / (μ : ℝ) * k ^ 2 := hfreq_sq
        _ = k ^ 2 * ((T : ℝ) / (μ : ℝ)) := by ring
        _ = ((n : ℝ) * π / (L : ℝ)) ^ 2 * ((T : ℝ) / (μ : ℝ)) := by
          simp only [k]
        _ = ((n : ℝ) * π / (L : ℝ)) ^ 2 * (√((T : ℝ) / (μ : ℝ))) ^ 2 := by
          congr 1
          apply (sq_sqrt hTμ.le).symm
        _ = ((n : ℝ) * π / (L : ℝ) * √((T : ℝ) / (μ : ℝ))) ^ 2 := by
          ring
  have hf' : (f : ℝ) = 2 * π * (f : ℝ) / (2 * π) := by
    field_simp [h2π]
  rw [hf', hside]
  field_simp [h2π, hL', hπ]


-- created on 2026-11-05
