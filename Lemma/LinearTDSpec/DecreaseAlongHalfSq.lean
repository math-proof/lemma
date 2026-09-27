import sympy.stats.linear_td
import sympy.stats.lyapunov
import sympy.vector.lp_space
import sympy.Basic
import sympy.core.singleton
import Lemma.Matrix.PosDefAsymm.is.Any_All_Le_Dot_MulVec
import Lemma.LinearTDSpec.NegDefAsymmA
import Lemma.LinearTDSpec.ExpectedUpdate.eq.ToLpAddMulVecA
open Matrix LpSpace


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {spec : LinearTDSpec S d} :
-- imply
  DecreaseAlong (fun x : EuclideanVec d => half_sq (ofL2 2 x)) (fun x => (half_sq' (ofL2 2 x)).toL2) spec.expected_update_target := by
-- proof
  obtain ⟨η, hη⟩ := (Matrix.PosDefAsymm.is.Any_All_Le_Dot_MulVec (-spec.A)).1 (LinearTDSpec.NegDefAsymmA (spec := spec)).nd
  refine ⟨⟨2 * η, mul_pos two_pos η.2, fun z hz x => ?_⟩⟩
  have hz' : spec.A *ᵥ WithLp.ofLp z + spec.b = 0 := by
    have h₀ : spec.expected_update z = 0 := by
      have h₁ : z = spec.expected_update z + z := hz
      simpa using h₁.symm
    rw [LinearTDSpec.ExpectedUpdate.eq.ToLpAddMulVecA] at h₀
    exact congrArg WithLp.ofLp h₀
  have hfx : spec.expected_update_target x - x = WithLp.toLp 2 (spec.A *ᵥ WithLp.ofLp (x - z)) := by
    rw [LinearTDSpec.expected_update_target, Pi.add_apply, id, add_sub_cancel_right, LinearTDSpec.ExpectedUpdate.eq.ToLpAddMulVecA, ← sub_zero (spec.A *ᵥ WithLp.ofLp x + spec.b), ← hz',
      WithLp.ofLp_sub, mulVec_sub, add_sub_add_right_eq_sub]
  have hg : (half_sq' (ofL2 2 (x - z))).toL2 = x - z := by
    ext i
    simp [half_sq', toL2, ofL2]
  have hn : ‖x - z‖ ^ 2 = WithLp.ofLp (x - z) ⬝ᵥ WithLp.ofLp (x - z) := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  have hi : inner ℝ (x - z) (WithLp.toLp 2 (spec.A *ᵥ WithLp.ofLp (x - z))) = WithLp.ofLp (x - z) ⬝ᵥ (spec.A *ᵥ WithLp.ofLp (x - z)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial, dotProduct_comm]
  have h₂ := hη (WithLp.ofLp (x - z))
  rw [neg_mulVec, dotProduct_neg] at h₂
  show inner ℝ ((half_sq' (ofL2 2 (x - z))).toL2) (spec.expected_update_target x - x) ≤ -(2 * η) * (1 / 2 * ‖x - z‖ ^ 2)
  rw [hg, hfx, hi, hn]
  linarith


-- created on 2026-09-26
