import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Exp

/-! LSTM recurrence (py `LSTM` / `LSTMCell`).  The `4 d_h` gate columns of py's `W`, `W_h`, `b`
(slices `[:d_h]`, `[d_h:2d_h]`, `[2d_h:3d_h]`, `[-d_h:]`) are indexed by `(gate, unit) : Fin 4 × Fin d_h`
with gates `0 = i`, `1 = f`, `2 = c`, `3 = o`.  The initial states are `h 0 = c 0 = 0`; step `t ≥ 1`
reads `x t`. -/

noncomputable def sigmoid (z : ℝ) : ℝ := 1 / (1 + Real.exp (-z))

/-- Pre-activation of gate `g`: `x_t @ W_g + h_{t-1} @ W_hg + b_g`. -/
def lstmGate {dx dh : ℕ} (W : Matrix (Fin dx) (Fin 4 × Fin dh) ℝ) (Wh : Matrix (Fin dh) (Fin 4 × Fin dh) ℝ)
    (b : Fin 4 × Fin dh → ℝ) (g : Fin 4) (xt : Fin dx → ℝ) (hprev : Fin dh → ℝ) (u : Fin dh) : ℝ :=
  ∑ a, xt a * W a (g, u) + ∑ a, hprev a * Wh a (g, u) + b (g, u)

/-- `(h t, c t)`. -/
noncomputable def lstm {dx dh : ℕ} (W : Matrix (Fin dx) (Fin 4 × Fin dh) ℝ) (Wh : Matrix (Fin dh) (Fin 4 × Fin dh) ℝ)
    (b : Fin 4 × Fin dh → ℝ) (x : ℕ → Fin dx → ℝ) : ℕ → (Fin dh → ℝ) × (Fin dh → ℝ)
  | 0 => (0, 0)
  | t + 1 =>
    let p := lstm W Wh b x t
    let c' : Fin dh → ℝ := fun u => sigmoid (lstmGate W Wh b 1 (x (t + 1)) p.1 u) * p.2 u +
      sigmoid (lstmGate W Wh b 0 (x (t + 1)) p.1 u) * Real.tanh (lstmGate W Wh b 2 (x (t + 1)) p.1 u)
    (fun u => sigmoid (lstmGate W Wh b 3 (x (t + 1)) p.1 u) * Real.tanh (c' u), c')


-- created on 2026-09-27
