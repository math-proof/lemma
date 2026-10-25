/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBondUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterSingleBondUpper.Part2
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoBondUpper.Part2
open Set
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

open StatMech.Sharpness


variable {V : Type*} [Fintype V] [DecidableEq V]


theorem twoReplicaTwoBridgeMoment_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) (r : Real) :
    twoReplicaTwoBridgeMoment G J hf x y r =
      Real.cosh r ^ 2 +
        (Real.cosh r * Real.sinh r) *
          ((expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 +
            (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2) +
        Real.sinh r ^ 2 *
          (expJ G.edgeFinset J hf
            (fun s => spin s x * spin s y)) ^ 2 := by
  let cx := Real.cosh r
  let sx := Real.sinh r
  have hexpand :
      (fun a b : ConfigSpace V => Real.exp (r *
        (spin a x * spin b x + spin a y * spin b y))) =
      (fun a b =>
        cx ^ 2 * ((1 : Real) * 1) +
          (cx * sx) * (spin a x * spin b x) +
          (cx * sx) * (spin a y * spin b y) +
          sx ^ 2 *
            ((spin a x * spin a y) * (spin b x * spin b y))) := by
    funext a b
    have hx : spin a x * spin b x = 1 ∨
        spin a x * spin b x = -1 := by
      rcases spin_eq_pm a x with ha | ha <;>
        rcases spin_eq_pm b x with hb | hb <;> simp [ha, hb]
    have hy : spin a y * spin b y = 1 ∨
        spin a y * spin b y = -1 := by
      rcases spin_eq_pm a y with ha | ha <;>
        rcases spin_eq_pm b y with hb | hb <;> simp [ha, hb]
    rw [mul_add, Real.exp_add, exp_mul_pm _ _ hx, exp_mul_pm _ _ hy]
    dsimp [cx, sx]
    ring
  have hone : ghsiExp2 G J hf (fun _ _ => (1 : Real)) = 1 := by
    have h := ghsiExp2_factor G J hf
      (fun _ => (1 : Real)) (fun _ => (1 : Real))
    simpa [expJ_one G J hf] using h
  unfold twoReplicaTwoBridgeMoment
  rw [hexpand]
  simp only [ghsiExp2_add, ghsiExp2_const_mul, ghsiExp2_factor]
  rw [hone]
  dsimp [cx, sx]
  ring


theorem expJ_monomial_le_one
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hf : V -> Real)
    (f : ConfigSpace V -> Real) (hfpm : forall s, f s <= 1) :
    expJ E J hf f <= 1 := by
  unfold expJ
  have hZ : 0 < ZJ E J hf := ZJ_pos E J hf
  rw [div_le_one hZ]
  unfold ZJ
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_of_le_one_left (wJ_nonneg E J hf s) (hfpm s)


theorem twoReplicaTwoBridgeFreeEnergy_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) (K : Real) :
    twoReplicaTwoBridgeFreeEnergy G J hf x y K =
      twoBondInterfaceFreeEnergy K
        (expJ G.edgeFinset J hf (fun s => spin s x))
        (expJ G.edgeFinset J hf (fun s => spin s y))
        (expJ G.edgeFinset J hf (fun s => spin s x * spin s y)) := by
  let mx := expJ G.edgeFinset J hf (fun s => spin s x)
  let my := expJ G.edgeFinset J hf (fun s => spin s y)
  let cxy := expJ G.edgeFinset J hf (fun s => spin s x * spin s y)
  let t := Real.tanh K
  let Pplus := 1 + t * (mx ^ 2 + my ^ 2) + t ^ 2 * cxy ^ 2
  let Pminus := 1 - t * (mx ^ 2 + my ^ 2) + t ^ 2 * cxy ^ 2
  have hcosh : 0 < Real.cosh K ^ 2 := sq_pos_of_pos (Real.cosh_pos K)
  have hplus : twoReplicaTwoBridgeMoment G J hf x y K =
      Real.cosh K ^ 2 * Pplus := by
    rw [twoReplicaTwoBridgeMoment_eq]
    dsimp [Pplus, t, mx, my, cxy]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos K).ne']
  have hminus : twoReplicaTwoBridgeMoment G J hf x y (-K) =
      Real.cosh K ^ 2 * Pminus := by
    rw [twoReplicaTwoBridgeMoment_eq]
    dsimp [Pminus, t, mx, my, cxy]
    rw [Real.cosh_neg, Real.sinh_neg, Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos K).ne']
    ring
  have hmoment_pos (r : Real) :
      0 < twoReplicaTwoBridgeMoment G J hf x y r := by
    unfold twoReplicaTwoBridgeMoment ghsiExp2
    apply div_pos
    · apply Finset.sum_pos
      · intro a _
        apply Finset.sum_pos
        · intro b _
          exact mul_pos (mul_pos (wJ_pos _ _ _ _) (wJ_pos _ _ _ _))
            (Real.exp_pos _)
        · exact Finset.univ_nonempty
      · exact Finset.univ_nonempty
    · exact sq_pos_of_pos (ZJ_pos _ _ _)
  have hPplus : 0 < Pplus := by
    have hp := hmoment_pos K
    rw [hplus] at hp
    exact pos_of_mul_pos_right hp hcosh.le
  have hPminus : 0 < Pminus := by
    have hp := hmoment_pos (-K)
    rw [hminus] at hp
    exact pos_of_mul_pos_right hp hcosh.le
  unfold twoReplicaTwoBridgeFreeEnergy twoBondInterfaceFreeEnergy
  rw [hplus, hminus, Real.log_mul hcosh.ne' hPplus.ne',
    Real.log_mul hcosh.ne' hPminus.ne']
  dsimp [Pplus, Pminus, t, mx, my, cxy]
  rw [Real.log_div hPplus.ne' hPminus.ne']
  ring


theorem twoReplicaTwoBridgeFreeEnergy_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    (x y : V) (hxy : x ≠ y) (K : Real) (hK : 0 <= K) :
    twoReplicaTwoBridgeFreeEnergy G J hf x y K <=
      2 * K *
        ((expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 +
          (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2) := by
  let mx := expJ G.edgeFinset J hf (fun s => spin s x)
  let my := expJ G.edgeFinset J hf (fun s => spin s y)
  let cxy := expJ G.edgeFinset J hf (fun s => spin s x * spin s y)
  have hmx0 : 0 <= mx := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e he => hJ e) hhf {x}
    rw [spinProd_singleton] at h
    exact h
  have hmy0 : 0 <= my := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e he => hJ e) hhf {y}
    rw [spinProd_singleton] at h
    exact h
  have hc0 : 0 <= cxy := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e he => hJ e) hhf {x, y}
    rw [spinProd_pair x y hxy] at h
    exact h
  have hmx1 : mx <= 1 := by
    apply expJ_monomial_le_one
    intro s
    rcases spin_eq_pm s x with h | h <;> rw [h] <;> norm_num
  have hmy1 : my <= 1 := by
    apply expJ_monomial_le_one
    intro s
    rcases spin_eq_pm s y with h | h <;> rw [h] <;> norm_num
  have hc1 : cxy <= 1 := by
    apply expJ_monomial_le_one
    intro s
    rcases spin_eq_pm s x with hx | hx <;>
      rcases spin_eq_pm s y with hy | hy <;> rw [hx, hy] <;> norm_num
  have hgks : mx * my <= cxy := by
    have h := gks_second_J G.edgeFinset J hf
      (fun e he => hJ e) hhf {x} {y}
    rw [spinProd_singleton, spinProd_singleton,
      symmDiff_singleton_pair x y hxy, spinProd_pair x y hxy] at h
    exact h
  rw [twoReplicaTwoBridgeFreeEnergy_eq]
  exact twoBondInterfaceFreeEnergy_le hK hmx0 hmx1 hmy0 hmy1 hc0 hc1 hgks

end
end StatMech.Ising
