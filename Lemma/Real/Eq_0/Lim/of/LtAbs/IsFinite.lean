import Lemma.Int.Lt.of.LtAbs
import Lemma.Int.Gt.of.LtAbs
import Lemma.Set.In.Icc.of.Lt.Gt
import Lemma.Real.Eq_0.Lim.of.In_Icc.IsFinite
import Lemma.Real.Eq_0.Lim.of.In_Icc.IsFinite.negative
open Filter Topology


@[main]
private lemma main
  {ℓ : ℝ}
  {x : ℕ → ℝ}
-- given
  (h₀ : |ℓ| < 1)
  (h₁ : BddAbove (Set.range fun n => |x n|)) :
-- imply
  lim [n → ∞] ℓ ^ n * x n = 0 := by
-- proof
  rcases lt_trichotomy ℓ 0 with h_lt | h_eq | h_gt
  · have h₂ := Int.Gt.of.LtAbs h₀
    have h₃ := Set.In.Icc.of.Lt.Gt h_lt h₂
    exact Real.Eq_0.Lim.of.In_Icc.IsFinite.negative h₃ h₁
  · subst h_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [zero_pow (by omega : n ≠ 0)]
  · have h₂ := Int.Lt.of.LtAbs h₀
    have h₃ := Set.In.Icc.of.Lt.Gt h₂ h_gt
    exact Real.Eq_0.Lim.of.In_Icc.IsFinite h₃ h₁


-- created on 2026-09-26
