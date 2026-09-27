import sympy.stats.linear_td
import sympy.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Lemma.LpSpace.MeasurableHalfSq.of.Ge_1
import Lemma.LpSpace.MeasurableHalfSq'.of.Ge_1
import Lemma.LinearTDSpec.MeasurableUncurryUpdateTarget
import Lemma.LinearTDSpec.Any_Ge_0AndAll_All_LeNormSubUpdateTarget_MulNormSub
import Lemma.LinearTDSpec.ExpectedUpdateTarget.eq.Sum_Sum_SMul
import Lemma.LinearTDSpec.ExpectedUpdateTdFixedPoint.eq.Zero
import Lemma.LinearTDSpec.LyapunovFunctionHalfSq
import Lemma.Iterates.AeTendsto.of.LyapunovFunction.Measurable.Measurable.All_Eq_Sum_Sum_SMul.Eq.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.MeasurableUncurry.IteratesOfResidual.Lt_1.Gt_Div2'3
open Filter Topology


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {spec : LinearTDSpec S d}
  {w : ℕ → (ℕ → S × S) → EuclideanVec d}
  {ν : ℝ}
-- given
  (h₀ : 2 / 3 < ν)
  (h₁ : ν < 1)
  (h₂ : LinearTDIterates spec w)
  (h₃ : spec.α = fun n : ℕ => inv_poly ν 2 n) :
-- imply
  ∀ᵐ ω ∂spec.markov_samples, Tendsto (fun n => w n ω) atTop (𝓝 spec.td_fixed_point) :=
-- proof
  Iterates.AeTendsto.of.LyapunovFunction.Measurable.Measurable.All_Eq_Sum_Sum_SMul.Eq.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.MeasurableUncurry.IteratesOfResidual.Lt_1.Gt_Div2'3 (MRP := spec.toFiniteMRP) h₀ h₁
    ⟨h₂.init, fun n ω => by rw [h₂.step, h₃, LinearTDSpec.update_target, add_sub_cancel_right]⟩
    (LinearTDSpec.MeasurableUncurryUpdateTarget (spec := spec)) LinearTDSpec.Any_Ge_0AndAll_All_LeNormSubUpdateTarget_MulNormSub
    (by rw [LinearTDSpec.expected_update_target, Pi.add_apply, LinearTDSpec.ExpectedUpdateTdFixedPoint.eq.Zero, zero_add]; rfl) LinearTDSpec.ExpectedUpdateTarget.eq.Sum_Sum_SMul
    (LpSpace.MeasurableHalfSq.of.Ge_1 (p := 2) (d := d) (by norm_num)) (LpSpace.MeasurableHalfSq'.of.Ge_1 (p := 2) (d := d) (by norm_num)) LinearTDSpec.LyapunovFunctionHalfSq


-- created on 2026-09-26
