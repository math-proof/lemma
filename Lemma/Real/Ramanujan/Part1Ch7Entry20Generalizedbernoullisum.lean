import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.Ramanujan.Part1Ch7Entry20Generalizedbernoullisum
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry20Generalizedbernoullisum


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[a2_eq_neg_a1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma a2_eq_neg_a1 : a2 = -a1 := by
  unfold a2 a1
  have h23 : (2/3 : ℝ) = -(1/3 : ℝ) + 1 := by norm_num
  rw [h23, AddCircle.coe_add_period (1 : ℝ) (-(1/3 : ℝ))]
  exact AddCircle.coe_neg (1 : ℝ) (x := (1/3 : ℝ))

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[phiArg1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma phiArg1 :
  ((((⟨-1/3, by change (-1 : ℝ) < -1 / 3 ∧ (-1 / 3 : ℝ) < 0; norm_num⟩ :
    Chapter7PhiArgument) : ℝ) + 1 : ℝ) : UnitAddCircle) = a2 := by
  unfold a2
  congr 1
  norm_num

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[phiArg2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma phiArg2 :
  ((((⟨-2/3, by change (-1 : ℝ) < -2 / 3 ∧ (-2 / 3 : ℝ) < 0; norm_num⟩ :
    Chapter7PhiArgument) : ℝ) + 1 : ℝ) : UnitAddCircle) = a1 := by
  unfold a1
  congr 1
  norm_num

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[phi_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma phi_sub (s : ℂ) (x y : Chapter7PhiArgument) :
  chapter7Phi s x - chapter7Phi s y =
    HurwitzZeta.hurwitzZeta (((y : ℝ) + 1 : ℝ) : UnitAddCircle) (-s) -
      HurwitzZeta.hurwitzZeta (((x : ℝ) + 1 : ℝ) : UnitAddCircle) (-s) := by
  unfold chapter7Phi
  ring

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[leftInner](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma leftInner (r : ℂ) :
  chapter7Phi (r - 1) ⟨-1 / 3, by change (-1 : ℝ) < -1 / 3 ∧ (-1 / 3 : ℝ) < 0; norm_num⟩ -
    chapter7Phi (r - 1) ⟨-2 / 3, by change (-1 : ℝ) < -2 / 3 ∧ (-2 / 3 : ℝ) < 0; norm_num⟩ =
    HurwitzZeta.hurwitzZeta a1 (1 - r) - HurwitzZeta.hurwitzZeta a2 (1 - r) := by
  have h := phi_sub (r - 1)
    (⟨-1 / 3, by change (-1 : ℝ) < -1 / 3 ∧ (-1 / 3 : ℝ) < 0; norm_num⟩ : Chapter7PhiArgument)
    (⟨-2 / 3, by change (-1 : ℝ) < -2 / 3 ∧ (-2 / 3 : ℝ) < 0; norm_num⟩ : Chapter7PhiArgument)
  rw [phiArg1, phiArg2] at h
  have hneg : -((r : ℂ) - 1) = 1 - r := by ring
  rwa [hneg] at h

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[rightInner](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma rightInner (r : ℂ) :
  chapter7Phi (-r) ⟨-1 / 3, by change (-1 : ℝ) < -1 / 3 ∧ (-1 / 3 : ℝ) < 0; norm_num⟩ -
    chapter7Phi (-r) ⟨-2 / 3, by change (-1 : ℝ) < -2 / 3 ∧ (-2 / 3 : ℝ) < 0; norm_num⟩ =
    HurwitzZeta.hurwitzZeta a1 r - HurwitzZeta.hurwitzZeta a2 r := by
  have h := phi_sub (-r)
    (⟨-1 / 3, by change (-1 : ℝ) < -1 / 3 ∧ (-1 / 3 : ℝ) < 0; norm_num⟩ : Chapter7PhiArgument)
    (⟨-2 / 3, by change (-1 : ℝ) < -2 / 3 ∧ (-2 / 3 : ℝ) < 0; norm_num⟩ : Chapter7PhiArgument)
  rw [phiArg1, phiArg2] at h
  have hneg : -(-(r : ℂ)) = r := by ring
  rwa [hneg] at h

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[Hdiff_eq_two_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma Hdiff_eq_two_odd (s : ℂ) :
  HurwitzZeta.hurwitzZeta a1 s - HurwitzZeta.hurwitzZeta a2 s =
    2 * HurwitzZeta.hurwitzZetaOdd a1 s := by
  rw [a2_eq_neg_a1, HurwitzZeta.hurwitzZetaOdd_eq]
  ring

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[diffDiff1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma diffDiff1 : Differentiable ℂ
  (fun r : ℂ => HurwitzZeta.hurwitzZeta a1 (1 - r) - HurwitzZeta.hurwitzZeta a2 (1 - r)) := by
  have hbase := HurwitzZeta.differentiable_hurwitzZeta_sub_hurwitzZeta a1 a2
  have haff : Differentiable ℂ (fun r : ℂ => 1 - r) :=
    (differentiable_const 1).sub differentiable_id
  exact hbase.comp haff

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[diffDiff2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma diffDiff2 :
  Differentiable ℂ (fun r : ℂ => HurwitzZeta.hurwitzZeta a1 r - HurwitzZeta.hurwitzZeta a2 r) :=
  HurwitzZeta.differentiable_hurwitzZeta_sub_hurwitzZeta a1 a2

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[baseNeZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma baseNeZero : (((6 * Real.pi : ℝ)) : ℂ) ≠ 0 := by
  have h6 : (0 : ℝ) < 6 * Real.pi := by positivity
  exact_mod_cast ne_of_gt h6

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[cpowDiff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma cpowDiff :
  Differentiable ℂ (fun r : ℂ => Complex.cpow (((6 * Real.pi : ℝ)) : ℂ) r) := by
  have h : NeZero (((6 * Real.pi : ℝ)) : ℂ) := ⟨baseNeZero⟩
  exact differentiable_const_cpow_of_neZero _

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[sinDiff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma sinDiff : Differentiable ℂ (fun r : ℂ => Complex.sin (Real.pi * r / 2)) := by
  have haff : Differentiable ℂ (fun r : ℂ => Real.pi * r / 2) := by
    exact ((differentiable_const (Real.pi : ℂ)).mul differentiable_id).div_const 2
  exact Complex.differentiable_sin.comp haff

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[meroLeft](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma meroLeft : MeromorphicOn chapter7Entry20Left Set.univ := by
  have hEq : chapter7Entry20Left = (fun r : ℂ =>
    Complex.cpow (((6 * Real.pi : ℝ)) : ℂ) r /
      ((((2 * Real.sqrt 3 : ℝ)) : ℂ) * Complex.Gamma r) *
      (HurwitzZeta.hurwitzZeta a1 (1 - r) - HurwitzZeta.hurwitzZeta a2 (1 - r))) := by
    funext r
    simp only [chapter7Entry20Left, leftInner]
  rw [hEq]
  apply MeromorphicOn.mul
  · apply MeromorphicOn.div
    · exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr cpowDiff).meromorphicOn
    · apply MeromorphicOn.mul
      · exact analyticOnNhd_const.meromorphicOn
      · exact MeromorphicOn.Gamma
  · exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr diffDiff1).meromorphicOn

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[meroRight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma meroRight : MeromorphicOn chapter7Entry20Right Set.univ := by
  have hEq : chapter7Entry20Right = (fun r : ℂ =>
    Complex.sin (Real.pi * r / 2) *
      (HurwitzZeta.hurwitzZeta a1 r - HurwitzZeta.hurwitzZeta a2 r)) := by
    funext r
    simp only [chapter7Entry20Right, rightInner]
  rw [hEq]
  apply MeromorphicOn.mul
  · exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr sinDiff).meromorphicOn
  · exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr diffDiff2).meromorphicOn

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[sin_3k](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma sin_3k (k : ℕ) : Real.sin (2 * Real.pi * (1/3 : ℝ) * ((3 * k : ℕ) : ℝ)) = 0 := by
  have harg : 2 * Real.pi * (1/3 : ℝ) * ((3 * k : ℕ) : ℝ) = (k : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg]
  have : Real.sin ((k : ℝ) * (2 * Real.pi)) = Real.sin (0 + (k : ℝ) * (2 * Real.pi)) := by
    rw [zero_add]
  rw [this, Real.sin_add_nat_mul_two_pi 0 k, Real.sin_zero]

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[sin_3k1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma sin_3k1 (k : ℕ) :
  Real.sin (2 * Real.pi * (1/3 : ℝ) * ((3 * k + 1 : ℕ) : ℝ)) = Real.sqrt 3 / 2 := by
  have harg : 2 * Real.pi * (1/3 : ℝ) * ((3 * k + 1 : ℕ) : ℝ) =
    2 * Real.pi / 3 + (k : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg, Real.sin_add_nat_mul_two_pi]
  have h23 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h23, Real.sin_pi_sub, Real.sin_pi_div_three]

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[sin_3k2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma sin_3k2 (k : ℕ) :
  Real.sin (2 * Real.pi * (1/3 : ℝ) * ((3 * k + 2 : ℕ) : ℝ)) = -(Real.sqrt 3 / 2) := by
  have harg : 2 * Real.pi * (1/3 : ℝ) * ((3 * k + 2 : ℕ) : ℝ) =
    Real.pi / 3 + Real.pi + (k : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg]
  have hstep : Real.sin (Real.pi / 3 + Real.pi + (k : ℝ) * (2 * Real.pi)) =
    Real.sin (Real.pi / 3 + Real.pi) := by
    have : Real.pi / 3 + Real.pi + (k : ℝ) * (2 * Real.pi) =
      (Real.pi / 3 + Real.pi) + (k : ℝ) * (2 * Real.pi) := by ring
    rw [this, Real.sin_add_nat_mul_two_pi]
  rw [hstep, Real.sin_add_pi, Real.sin_pi_div_three]

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[block_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma block_eq (s : ℂ) (k : ℕ) :
  (useries s (3 * k) + useries s (3 * k + 1) + useries s (3 * k + 2)) =
    ↑(Real.sqrt 3 / 2) * fseries s k := by
  unfold useries fseries
  rw [sin_3k k, sin_3k1 k, sin_3k2 k]
  simp only [Complex.ofReal_zero, zero_div]
  push_cast
  ring

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[term_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma term_eq (n : ℕ) (s : ℂ) :
  oddseries s n = (3 : ℂ) ^ s / 2 * fseries s n := by
  unfold oddseries fseries
  have r1 : (n : ℝ) + 1/3 = (((3 * n + 1 : ℕ) : ℝ)) / 3 := by
    push_cast
    ring
  have r2 : (n : ℝ) + 1 - 1/3 = (((3 * n + 2 : ℕ) : ℝ)) / 3 := by
    push_cast
    ring
  have h1 : ((((n : ℝ) + 1/3 : ℝ)) : ℂ) = ((n : ℂ) + ((1/3 : ℝ) : ℂ)) := by
    rw [Complex.ofReal_add, Complex.ofReal_natCast]
  have h2 : ((((n : ℝ) + 1 - 1/3 : ℝ)) : ℂ) = ((n : ℂ) + 1 - ((1/3 : ℝ) : ℂ)) := by
    rw [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  have e1 : ((n : ℂ) + ((1/3 : ℝ) : ℂ)) = (((((3 * n + 1 : ℕ) : ℝ)) / 3 : ℝ) : ℂ) := by
    rw [← h1, r1]
  have e2 : ((n : ℂ) + 1 - ((1/3 : ℝ) : ℂ)) = (((((3 * n + 2 : ℕ) : ℝ)) / 3 : ℝ) : ℂ) := by
    rw [← h2, r2]
  have hN1 : (0 : ℝ) ≤ (((3 * n + 1 : ℕ) : ℝ)) := by positivity
  have hN2 : (0 : ℝ) ≤ (((3 * n + 2 : ℕ) : ℝ)) := by positivity
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  rw [e1, e2]
  simp only [Complex.ofReal_div]
  rw [Complex.div_cpow_ofReal_nonneg hN1 h3, Complex.div_cpow_ofReal_nonneg hN2 h3]
  simp only [Complex.ofReal_natCast, Complex.ofReal_ofNat, one_div_div]
  ring

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[blk_inj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma blk_inj : Function.Injective blk := by
  intro p q h
  obtain ⟨a, i⟩ := p
  obtain ⟨b, j⟩ := q
  simp only [blk] at h
  have hi := i.isLt
  have hj := j.isLt
  have h2 : a = b ∧ i.val = j.val := by omega
  obtain ⟨hab, hij⟩ := h2
  subst hab
  have hij2 : i = j := Fin.ext hij
  subst hij2
  rfl

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[blk_surj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma blk_surj : Function.Surjective blk := by
  intro n
  exact ⟨(n / 3, ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩), Nat.div_add_mod n 3⟩

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[blk_bij](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma blk_bij : Function.Bijective blk :=
  ⟨blk_inj, blk_surj⟩

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[inner_block](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma inner_block (s : ℂ) (k : ℕ) :
  (∑' i : Fin 3, useries s (blk (k, i))) =
    useries s (3 * k) + useries s (3 * k + 1) + useries s (3 * k + 2) := by
  rw [tsum_fintype, Fin.sum_univ_three]
  simp only [blk, Fin.val_zero, Fin.val_one]
  have h2 : ((2 : Fin 3).val) = 2 := rfl
  rw [h2, add_zero]

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[fiber_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma fiber_tsum (s : ℂ) (hu : Summable (useries s)) :
  (∑' n, useries s n) =
    ∑' k : ℕ, (useries s (3 * k) + useries s (3 * k + 1) + useries s (3 * k + 2)) := by
  have hcomp : Summable (fun p : ℕ × Fin 3 => useries s (blk p)) :=
    hu.comp_injective blk_inj
  have hfib : ∀ k : ℕ, Summable (fun i : Fin 3 => useries s (blk (k, i))) :=
    fun k => (hasSum_fintype _).summable
  have h1 : (∑' n, useries s n) = ∑' p : ℕ × Fin 3, useries s (blk p) :=
    (Equiv.tsum_eq (Equiv.ofBijective blk blk_bij) (useries s)).symm
  have h2 : (∑' p : ℕ × Fin 3, useries s (blk p)) =
    ∑' k : ℕ, ∑' i : Fin 3, useries s (blk (k, i)) :=
    Summable.tsum_prod' hcomp hfib
  have h3 : (∑' k : ℕ, ∑' i : Fin 3, useries s (blk (k, i))) =
    ∑' k : ℕ, (useries s (3 * k) + useries s (3 * k + 1) + useries s (3 * k + 2)) :=
    tsum_congr (fun k => inner_block s k)
  rw [h1, h2, h3]

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[triplication](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma triplication {s : ℂ} (hs : 1 < s.re) :
  HurwitzZeta.hurwitzZetaOdd a1 s =
    (3 : ℂ) ^ s / ((Real.sqrt 3 : ℝ) : ℂ) * HurwitzZeta.sinZeta a1 s := by
  have hmem : (1/3 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have huH : HasSum (useries s) (HurwitzZeta.sinZeta a1 s) :=
    HurwitzZeta.hasSum_nat_sinZeta (1/3 : ℝ) hs
  have htH : HasSum (oddseries s) (HurwitzZeta.hurwitzZetaOdd a1 s) :=
    HurwitzZeta.hasSum_nat_hurwitzZetaOdd_of_mem_Icc hmem hs
  have hsqrt : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < Real.sqrt 3 := by positivity
    exact_mod_cast ne_of_gt hpos
  have hconv : ((Real.sqrt 3 / 2 : ℝ) : ℂ) = ((Real.sqrt 3 : ℝ) : ℂ) / 2 := by
    push_cast
    ring
  have hOdd : HurwitzZeta.hurwitzZetaOdd a1 s =
    (3 : ℂ) ^ s / 2 * ∑' k, fseries s k := by
    rw [← htH.tsum_eq, tsum_congr (fun n => term_eq n s), tsum_mul_left]
  have hSin : HurwitzZeta.sinZeta a1 s =
    ((Real.sqrt 3 : ℝ) : ℂ) / 2 * ∑' k, fseries s k := by
    rw [← huH.tsum_eq, fiber_tsum s huH.summable, tsum_congr (fun k => block_eq s k),
      tsum_mul_left, hconv]
  rw [hOdd, hSin]
  field_simp

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[hLform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma hLform (r : ℂ) : chapter7Entry20Left r =
  ((((6*Real.pi:ℝ))):ℂ)^r / (((((2*Real.sqrt 3:ℝ))):ℂ) * Complex.Gamma r) *
    (2 * HurwitzZeta.hurwitzZetaOdd a1 (1 - r)) := by
  unfold chapter7Entry20Left
  rw [leftInner r, Hdiff_eq_two_odd]
  rfl

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[hRform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma hRform (r : ℂ) : chapter7Entry20Right r =
  Complex.sin (Real.pi * r / 2) * (2 * HurwitzZeta.hurwitzZetaOdd a1 r) := by
  unfold chapter7Entry20Right
  rw [rightInner r, Hdiff_eq_two_odd]

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[hFEform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma hFEform {r : ℂ} (hr : ∀ n : ℕ, r ≠ -((n : ℕ) : ℂ)) :
  HurwitzZeta.hurwitzZetaOdd a1 (1 - r) =
    2 * (2 * ((Real.pi:ℝ):ℂ)) ^ (-r) * Complex.Gamma r * Complex.sin (((Real.pi:ℝ):ℂ) * r / 2) *
      HurwitzZeta.sinZeta a1 r :=
  HurwitzZeta.hurwitzZetaOdd_one_sub a1 hr

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[hTripInv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma hTripInv {r : ℂ} (hs : 1 < r.re) (hBr : (3 : ℂ) ^ r ≠ 0)
  (hsqrt : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0) :
  HurwitzZeta.sinZeta a1 r =
    ((Real.sqrt 3:ℝ):ℂ) / (3:ℂ)^r * HurwitzZeta.hurwitzZetaOdd a1 r := by
  have hT := triplication hs
  rw [hT]
  field_simp

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[agree_on_Re_gt_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma agree_on_Re_gt_one {r : ℂ} (hs : 1 < r.re) :
  chapter7Entry20Left r = chapter7Entry20Right r := by
  have hr : ∀ n : ℕ, r ≠ -((n : ℕ) : ℂ) := by
    intro n h
    have hre : (1:ℝ) < r.re := hs
    rw [h] at hre
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have hn : (0:ℝ) ≤ ((n:ℕ):ℝ) := Nat.cast_nonneg n
    linarith
  have h2pi : ((((2 * Real.pi : ℝ))) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
    exact_mod_cast ne_of_gt hpos
  have h2pic : ((((2*Real.pi:ℝ))):ℂ) = 2 * (((Real.pi:ℝ)):ℂ) := by
    push_cast
    ring
  have h3c : ((((3:ℝ))):ℂ) = (3:ℂ) := by simp
  have h6 : ((((6*Real.pi:ℝ))):ℂ)^r = ((((2*Real.pi:ℝ))):ℂ)^r * ((((3:ℝ))):ℂ)^r := by
    have e : (6*Real.pi:ℝ) = (2*Real.pi)*(3:ℝ) := by ring
    rw [e, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) (by norm_num)]
  have hBr : (3:ℂ)^r ≠ 0 := by
    intro h
    rw [Complex.cpow_eq_zero_iff] at h
    norm_num at h
  have hAr : ((((2*Real.pi:ℝ))):ℂ)^r ≠ 0 := by
    intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact h2pi h.1
  have hG : Complex.Gamma r ≠ 0 := Complex.Gamma_ne_zero hr
  have hsqrt : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < Real.sqrt 3 := by positivity
    exact_mod_cast ne_of_gt hpos
  have hD : (((2 * Real.sqrt 3 : ℝ)) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < 2 * Real.sqrt 3 := by positivity
    exact_mod_cast ne_of_gt hpos
  have hL := hLform r
  have hR := hRform r
  have hFE := hFEform hr
  have hTripInv := hTripInv hs hBr hsqrt
  rw [hL, hR, hFE, ← h2pic, hTripInv, h6, h3c, Complex.cpow_neg]
  field_simp
  push_cast
  ring

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[hEqLeftProd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma hEqLeftProd : chapter7Entry20Left = (fun r : ℂ =>
  Complex.cpow ((((6*Real.pi:ℝ))):ℂ) r * ((((2*Real.sqrt 3:ℝ))):ℂ)⁻¹ *
    (Complex.Gamma r)⁻¹ *
    (HurwitzZeta.hurwitzZeta a1 (1 - r) - HurwitzZeta.hurwitzZeta a2 (1 - r))) := by
  funext r
  unfold chapter7Entry20Left
  rw [leftInner r, div_eq_mul_inv, mul_inv]
  ring

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[hLeftDiff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma hLeftDiff : Differentiable ℂ chapter7Entry20Left := by
  rw [hEqLeftProd]
  exact ((cpowDiff.mul (differentiable_const _)).mul
    Complex.differentiable_one_div_Gamma).mul diffDiff1

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[hRightDiff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma hRightDiff : Differentiable ℂ chapter7Entry20Right := by
  have hEq : chapter7Entry20Right = (fun r : ℂ =>
    Complex.sin (Real.pi * r / 2) *
      (HurwitzZeta.hurwitzZeta a1 r - HurwitzZeta.hurwitzZeta a2 r)) := by
    funext r
    simp only [chapter7Entry20Right, rightInner]
  rw [hEq]
  exact sinDiff.mul diffDiff2

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[hLeftAn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma hLeftAn : AnalyticOnNhd ℂ chapter7Entry20Left Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr hLeftDiff

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[hRightAn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma hRightAn : AnalyticOnNhd ℂ chapter7Entry20Right Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr hRightDiff

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[hNbhd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma hNbhd : chapter7Entry20Left =ᶠ[𝓝 (2:ℂ)] chapter7Entry20Right := by
  have hU : {s : ℂ | 1 < s.re} ∈ 𝓝 (2:ℂ) := by
    have h2 : (1:ℝ) < ((2:ℂ)).re := by simp
    have hmem : Set.Ioi (1:ℝ) ∈ nhds (((2:ℂ)).re) := Ioi_mem_nhds h2
    exact Complex.continuous_re.tendsto (2:ℂ) hmem
  filter_upwards [hU] with r hr using agree_on_Re_gt_one hr

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[hFunEq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma hFunEq : chapter7Entry20Left = chapter7Entry20Right :=
  AnalyticOnNhd.eq_of_eventuallyEq hLeftAn hRightAn hNbhd

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum

/--
[ramanujan_part1_ch7_entry20_generalizedbernoullisum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
lemma ramanujan_part1_ch7_entry20_generalizedbernoullisum
  :
-- imply
  MeromorphicOn chapter7Entry20Left Set.univ ∧
    MeromorphicOn chapter7Entry20Right Set.univ ∧
    chapter7Entry20Left =ᶠ[codiscrete ℂ] chapter7Entry20Right :=
-- proof
  ⟨meroLeft, meroRight, Filter.Eventually.of_forall (fun r => congrFun hFunEq r)⟩
end



-- created on 2026-10-20
-- updated on 2026-10-26
