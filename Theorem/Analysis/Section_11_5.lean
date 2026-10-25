import Mathlib
import Abbrev.Analysis.Section_9_9
import Theorem.Analysis.Section_11_4
/-!
# Analysis I, Section 11.5: Riemann integrability of continuous functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Riemann integrability of uniformly continuous functions.
- Riemann integrability of bounded continuous functions.

-/


namespace Chapter11

open BoundedInterval

open Chapter9

/-- Corollary 11.5.2 -/
theorem integ_of_cts {a b:ℝ} {f:ℝ → ℝ} (hf: ContinuousOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := integ_of_uniform_cts (UniformContinuousOn.of_continuousOn hf)

open PiecewiseConstantOn ConstantOn in
set_option maxHeartbeats 999999 in
/-- Proposition 11.5.3 -/
theorem integ_of_bdd_cts {I: BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: ContinuousOn f I) : IntegrableOn f I := by
  -- This proof is written to follow the structure of the original text.
  by_cases hsing : |I|ₗ = 0
  . exact (integ_on_subsingleton hsing).1
  have hI : (I:Set ℝ).Nonempty := by by_contra!; rw [←BoundedInterval.length_of_subsingleton] at hsing; simp_all
  simp at hsing
  set a := I.a
  set b := I.b
  have lower_le_upper := lower_integral_le_upper hbound
  have ⟨ M, hM ⟩ := hbound
  have hMpos : 0 ≤ M := (abs_nonneg _).trans (hM hI.some hI.some_mem)
  have (ε:ℝ) (hε: ε > 0) : upper_integral f I - lower_integral f I ≤ (4*M+2) * ε := by
    wlog hε' : ε < (b-a)/2
    . specialize this _ _ _ _ _ _ hM _ ((b-a)/3) _ _
        <;> first | assumption | linarith | apply this.trans; gcongr; linarith
    set I' := Icc (a+ε) (b-ε)
    set Ileft : BoundedInterval := match I with
    | Icc _ _ => Ico a (a + ε)
    | Ico _ _ => Ico a (a + ε)
    | Ioc _ _ => Ioo a (a + ε)
    | Ioo _ _ => Ioo a (a + ε)
    set Iright : BoundedInterval := match I with
    | Icc _ _ => Ioc (b - ε) b
    | Ico _ _ => Ioo (b - ε) b
    | Ioc _ _ => Ioc (b - ε) b
    | Ioo _ _ => Ioo (b - ε) b
    set Ileft' : BoundedInterval := match I with
    | Icc _ _ => Icc a (b - ε)
    | Ico _ _ => Icc a (b - ε)
    | Ioc _ _ => Ioc a (b - ε)
    | Ioo _ _ => Ioc a (b - ε)
    have Ileftlen : |Ileft|ₗ = ε := by cases I <;> simp [Ileft, length, le_of_lt hε]
    have Irightlen : |Iright|ₗ = ε := by cases I <;> simp [Iright, length, le_of_lt hε]
    have hjoin1 : Ileft'.joins Ileft I' := by
      cases I
      case Icc _ _ => apply join_Ico_Icc <;> linarith
      case Ico _ _ => apply join_Ico_Icc <;> linarith
      case Ioc _ _ => apply join_Ioo_Icc <;> linarith
      case Ioo _ _ => apply join_Ioo_Icc <;> linarith
    have hjoin2: I.joins Ileft' Iright := by
      cases I
      case Icc _ _ => apply join_Icc_Ioc <;> linarith
      case Ico _ _ => apply join_Icc_Ioo <;> linarith
      case Ioc _ _ => apply join_Ioc_Ioc <;> linarith
      case Ioo _ _ => apply join_Ioc_Ioo <;> linarith
    have hf' : IntegrableOn f I' := by
      apply integ_of_cts $ ContinuousOn.mono hf $ subset_trans _ $ (subset_iff _ _).mp $ Ioo_subset I
      intro _; simp; grind
    choose h hhmin hhconst hhint using lt_of_gt_upper_integral hf'.1 (show upper_integral f I' < integ f I' + ε by linarith [hf'.2])
    classical
    set h' : ℝ → ℝ := fun x ↦ if x ∈ I' then h x else M
    have h'const_left (x:ℝ) (hx: x ∈ Ileft) : h' x = M := by
      replace hjoin1 := Set.eq_empty_iff_forall_notMem.mp hjoin1.1 x
      simp_all [h',mem_iff]
    have h'const_right (x:ℝ) (hx: x ∈ Iright) : h' x = M := by
      replace hjoin2 := Set.eq_empty_iff_forall_notMem.mp hjoin2.1 x
      replace hjoin1 := congrArg (x ∈ ·) hjoin1.2.1
      simp_all [h',mem_iff]
    have h'const : PiecewiseConstantOn h' I := by
      rw [of_join hjoin2, of_join hjoin1]; split_ands
      . apply_rules [piecewiseConstantOn, of_const]
      . apply hhconst.congr'; grind [mem_iff]
      apply_rules [piecewiseConstantOn, of_const]
    have h'maj : MajorizesOn h' f I := by
      intro x _; by_cases hxI': x ∈ I' <;> simp [h', hxI']; solve_by_elim; grind [abs_le']
    observe h'maj : upper_integral f I ≤ h'const.integ'
    have h'integ1 := h'const.integ_of_join hjoin2
    have h'integ2 := ((of_join hjoin2 _).mp h'const).1.integ_of_join hjoin1
    have h'integ3 : PiecewiseConstantOn.integ h' Ileft = M * ε := by
      rw [PiecewiseConstantOn.integ_congr h'const_left, integ_const, Ileftlen]
    have h'integ4 : PiecewiseConstantOn.integ h' Iright = M * ε := by
      rw [PiecewiseConstantOn.integ_congr h'const_right, integ_const, Irightlen]
    have h'integ5 : PiecewiseConstantOn.integ h' I' = PiecewiseConstantOn.integ h I' := by
      apply PiecewiseConstantOn.integ_congr; grind [mem_iff]
    choose g hgmin hgconst hgint using gt_of_lt_lower_integral hf'.1 (show integ f I' - ε < lower_integral f I' by linarith [hf'.2])
    set g' : ℝ → ℝ := fun x ↦ if x ∈ I' then g x else -M
    have g'const_left (x:ℝ) (hx: x ∈ Ileft) : g' x = -M := by
      replace hjoin1 := Set.eq_empty_iff_forall_notMem.mp hjoin1.1 x
      simp_all [g', mem_iff]
    have g'const_right (x:ℝ) (hx: x ∈ Iright) : g' x = -M := by
      replace hjoin2 := Set.eq_empty_iff_forall_notMem.mp hjoin2.1 x
      replace hjoin1 := congrArg (x ∈ ·) hjoin1.2.1
      simp_all [g', mem_iff]
    have g'const : PiecewiseConstantOn g' I := by
      rw [of_join hjoin2, of_join hjoin1]; split_ands
      . apply_rules [piecewiseConstantOn, of_const]
      . apply hgconst.congr'; grind [mem_iff]
      apply_rules [piecewiseConstantOn, of_const]
    have g'maj : MinorizesOn g' f I := by
      intro x _; by_cases hxI': x ∈ I' <;> simp [g', hxI']; solve_by_elim; grind [abs_le']
    observe g'maj : g'const.integ' ≤ lower_integral f I
    have g'integ1 := g'const.integ_of_join hjoin2
    have g'integ2 := ((of_join hjoin2 _).mp g'const).1.integ_of_join hjoin1
    have g'integ3 : PiecewiseConstantOn.integ g' Ileft = -M * ε := by
      rw [PiecewiseConstantOn.integ_congr g'const_left, integ_const, Ileftlen]
    have g'integ4 : PiecewiseConstantOn.integ g' Iright = -M * ε := by
      rw [PiecewiseConstantOn.integ_congr g'const_right, integ_const, Irightlen]
    have g'integ5 : PiecewiseConstantOn.integ g' I' = PiecewiseConstantOn.integ g I' := by
      apply PiecewiseConstantOn.integ_congr; grind [mem_iff]
    have h'join : PiecewiseConstantOn.integ h' I = M * ε + PiecewiseConstantOn.integ h I' + M * ε := by
      rw [h'integ1, h'integ2, h'integ3, h'integ4, h'integ5]
    have g'join : PiecewiseConstantOn.integ g' I = -M * ε + PiecewiseConstantOn.integ g I' + -M * ε := by
      rw [g'integ1, g'integ2, g'integ3, g'integ4, g'integ5]
    linarith [h'maj, g'maj, hhint, hgint, h'join, g'join]
  exact ⟨ hbound, by linarith [nonneg_of_le_const_mul_eps this] ⟩

end Chapter11
