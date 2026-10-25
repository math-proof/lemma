import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part4


noncomputable instance PreL1.inst_seminormedAddCommGroup {d:ℕ} : SeminormedAddCommGroup (PreL1 d) := {
  norm F := F.integrable.norm
  neg F := ⟨ -F.f, F.integrable.of_neg ⟩
  zsmul := zsmulRec
  neg_add_cancel := fun F => by
    apply PreL1.ext
    funext x
    show (-F.f + F.f) x = (0 : EuclideanSpace' d → ℂ) x
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, neg_add_cancel]
  dist_self := fun F => by
    -- dist F F = ‖-F + F‖ where (-F + F).f = -F.f + F.f
    -- The goal after simp has { f := -F.f, ... } + F which is syntactically different from -F + F
    -- We use convert to bridge the gap
    suffices h : ComplexAbsolutelyIntegrable.zero.norm = 0 from by
      convert h using 2
      funext x
      show (-F.f + F.f) x = (0 : EuclideanSpace' d → ℂ) x
      simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, neg_add_cancel]
    exact ComplexAbsolutelyIntegrable.norm_zero
  dist_comm := fun F G => by
    -- dist F G = ‖-F+G‖, dist G F = ‖-G+F‖
    simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
    congr 1; congr 1; funext x; simp only [EReal.abs_fun]; congr 1
    show ‖(-F.f + G.f) x‖ = ‖(-G.f + F.f) x‖
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [show -F.f x + G.f x = -(F.f x - G.f x) from by ring,
        show -G.f x + F.f x = -(G.f x - F.f x) from by ring,
        norm_neg, norm_neg, norm_sub_rev]
  dist_triangle := fun F G H => by
    -- dist F H ≤ dist F G + dist G H
    -- All use ‖-X + Y‖ form. We need to avoid simp expanding things.
    -- The norm of a PreL1 P is P.integrable.norm = (UnsignedLebesgueIntegral (EReal.abs_fun P.f)).toReal
    -- dist X Y = ‖-X + Y‖ = (-X + Y).integrable.norm
    -- Let's set up abbreviations that will definitionally match the goal
    let FH : PreL1 d := -F + H
    let FG : PreL1 d := -F + G
    let GH : PreL1 d := -G + H
    -- The goal is: FH.integrable.norm ≤ FG.integrable.norm + GH.integrable.norm
    show FH.integrable.norm ≤ FG.integrable.norm + GH.integrable.norm
    simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
    have h_eq : FH.f = FG.f + GH.f := by
      show (-F.f + H.f) = (-F.f + G.f) + (-G.f + H.f)
      funext x; simp only [Pi.add_apply, Pi.neg_apply]; ring
    have h_le : ∀ x, EReal.abs_fun FH.f x ≤ (EReal.abs_fun FG.f + EReal.abs_fun GH.f) x := fun x => by
      rw [h_eq]; simp only [EReal.abs_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_add_le (FG.f x) (GH.f x))
    have hfg_abs := FG.integrable.abs
    have hgh_abs := GH.integrable.abs
    have hfh_abs := FH.integrable.abs
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun FH.f) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun FG.f + EReal.abs_fun GH.f) := by
      apply LowerUnsignedLebesgueIntegral.mono hfh_abs.1 (UnsignedMeasurable.add hfg_abs.1 hgh_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun FG.f + EReal.abs_fun GH.f) =
                 UnsignedLebesgueIntegral (EReal.abs_fun FG.f) + UnsignedLebesgueIntegral (EReal.abs_fun GH.f) := by
      apply LowerUnsignedLebesgueIntegral.add hfg_abs.1 hgh_abs.1 (UnsignedMeasurable.add hfg_abs.1 hgh_abs.1)
    have h_ineq : UnsignedLebesgueIntegral (EReal.abs_fun FH.f) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun FG.f) + UnsignedLebesgueIntegral (EReal.abs_fun GH.f) := by
      rw [← h_add]; exact h_mono
    have h_finite_fh : UnsignedLebesgueIntegral (EReal.abs_fun FH.f) < ⊤ := hfh_abs.2
    have h_finite_fg : UnsignedLebesgueIntegral (EReal.abs_fun FG.f) < ⊤ := hfg_abs.2
    have h_finite_gh : UnsignedLebesgueIntegral (EReal.abs_fun GH.f) < ⊤ := hgh_abs.2
    have h_nonneg_fh : UnsignedLebesgueIntegral (EReal.abs_fun FH.f) ≠ ⊥ := by
      exact ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hfh_abs.1))
    have h_nonneg_fg : UnsignedLebesgueIntegral (EReal.abs_fun FG.f) ≠ ⊥ := by
      exact ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hfg_abs.1))
    have h_nonneg_gh : UnsignedLebesgueIntegral (EReal.abs_fun GH.f) ≠ ⊥ := by
      exact ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hgh_abs.1))
    have h_sum_ne_top : UnsignedLebesgueIntegral (EReal.abs_fun FG.f) + UnsignedLebesgueIntegral (EReal.abs_fun GH.f) ≠ ⊤ :=
      (EReal.add_lt_top h_finite_fg.ne_top h_finite_gh.ne_top).ne_top
    rw [← EReal.toReal_add h_finite_fg.ne_top h_nonneg_fg h_finite_gh.ne_top h_nonneg_gh]
    exact EReal.toReal_le_toReal h_ineq h_nonneg_fh h_sum_ne_top
}

instance PreL1.inst_normedSpace {d:ℕ} : NormedSpace ℂ (PreL1 d) := {
  norm_smul_le := fun a F => by
    -- Goal: ‖a • F‖ ≤ ‖a‖ * ‖F‖
    -- ‖F‖ = F.integrable.norm for PreL1
    show (a • F).integrable.norm ≤ ‖a‖ * F.integrable.norm
    simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
    -- Key fact: EReal.abs_fun (a • F.f) x = ‖a‖ * EReal.abs_fun F.f x
    have h_eq : ∀ x, EReal.abs_fun (a • F).f x = ‖a‖.toEReal * EReal.abs_fun F.f x := fun x => by
      simp only [EReal.abs_fun]
      -- Show ‖(a • F).f x‖ = ‖a‖ * ‖F.f x‖
      show (‖(a • F).f x‖ : EReal) = ‖a‖.toEReal * ‖F.f x‖.toEReal
      rw [show (a • F).f x = a * F.f x from rfl, norm_mul, EReal.coe_mul]
    have hf_abs := ComplexAbsolutelyIntegrable.abs F.f F.integrable
    have h_smul_eq : EReal.abs_fun (a • F).f = (fun x => ‖a‖.toEReal * EReal.abs_fun F.f x) := by
      funext x; exact h_eq x
    rw [h_smul_eq]
    have h_scale : UnsignedLebesgueIntegral (fun x => ‖a‖.toEReal * EReal.abs_fun F.f x) =
                   ‖a‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun F.f) := by
      have h_eq' : (fun x => ‖a‖.toEReal * EReal.abs_fun F.f x) = (‖a‖.toEReal : EReal) • EReal.abs_fun F.f := by
        funext x; simp only [Pi.smul_apply, smul_eq_mul]
      rw [h_eq', UnsignedLebesgueIntegral]
      exact LowerUnsignedLebesgueIntegral.hom hf_abs.1 (norm_nonneg a)
    rw [h_scale]
    -- Now we have: (‖a‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun F.f)).toReal ≤ ‖a‖ * (UnsignedLebesgueIntegral (EReal.abs_fun F.f)).toReal
    -- We actually have equality
    have h_finite : UnsignedLebesgueIntegral (EReal.abs_fun F.f) < ⊤ := hf_abs.2
    have h_nonneg : 0 ≤ UnsignedLebesgueIntegral (EReal.abs_fun F.f) := UnsignedLebesgueIntegral.nonneg hf_abs.1
    have h_ne_bot : UnsignedLebesgueIntegral (EReal.abs_fun F.f) ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero h_nonneg)
    rw [EReal.toReal_mul]
    simp only [EReal.toReal_coe, le_refl]
}

