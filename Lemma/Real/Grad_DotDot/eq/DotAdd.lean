import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Initialize.Tactic.Attr.Basic
set_option linter.deprecated false


@[path]
private lemma main
  {n : ℕ} {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ} {k : Fin n} :
-- imply
  fderiv ℝ (fun y : Fin n → ℝ => ∑ i, ∑ j, y i * A i j * y j) x (Pi.single k (1 : ℝ)) =
    ∑ j, (A k j + A j k) * x j := by
-- proof
  have hfun : (fun y : Fin n → ℝ => ∑ i, ∑ j, y i * A i j * y j) =
      fun y => ∑ i, ∑ j, y i * (A i j * y j) := by
    funext y
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have hterm (i j : Fin n) :
    HasFDerivAt (fun y : Fin n → ℝ => y i * (A i j * y j))
      (x i • A i j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j +
        (A i j * x j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) x := by
    have happi := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) i x
    have happj := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) j x
    convert happi.mul (happj.const_mul (A i j)) using 1
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm i j))
  rw [hfun, hsum.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply]
  simp only [smul_eq_mul, mul_ite, mul_zero, mul_one, Finset.sum_add_distrib]
  have hpick (c : Fin n → ℝ) : ∑ j, (if j = k then c j else 0) = c k := by
    simp [Finset.mem_univ]
  have hleft : ∑ i, ∑ j, (if j = k then x i * A i j else 0) = ∑ i, x i * A i k := by
    refine Finset.sum_congr rfl ?_
    intro i _
    apply hpick
  have hright : ∑ i, ∑ j, (if i = k then A i j * x j else 0) = ∑ j, A k j * x j := by
    have hpull (i : Fin n) : ∑ j, (if i = k then A i j * x j else 0) =
        if i = k then ∑ j, A i j * x j else 0 := by
      if hik : i = k then
        simp [hik]
      else
        simp [hik]
    simp only [hpull]
    apply hpick
  rw [hleft, hright, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring


-- created on 2021-12-25
-- updated on 2026-10-26
