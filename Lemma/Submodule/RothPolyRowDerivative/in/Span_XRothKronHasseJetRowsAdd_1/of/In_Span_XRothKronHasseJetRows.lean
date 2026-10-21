import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.MvPolynomial.RothHelpers
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial
open MvPolynomial (rothMvHasse_coeff_h)


private lemma rothKronecker_X_h
  {m : ℕ} {K : Type*} [Field K]
  (D : ℕ)
  (h : Fin m) :
  rothKronecker D (MvPolynomial.X h : MvPolynomial (Fin m) K) =
    X ^ D ^ (h : ℕ) := by
  simp [rothKronecker]

private lemma rothKronecker_derivative_h
  {m : ℕ} {K : Type*} [Field K]
  (D : ℕ)
  (P : MvPolynomial (Fin m) K) :
  derivative (rothKronecker D P) =
    Finset.univ.sum fun h : Fin m =>
      C (D ^ (h : ℕ) : K) * X ^ (D ^ (h : ℕ) - 1) *
        rothKronecker D (MvPolynomial.pderiv h P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [rothKronecker]
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    ring
  | mul_X P n hP =>
    have hsecond :
      (∑ h : Fin m,
          C (D ^ (h : ℕ) : K) * X ^ (D ^ (h : ℕ) - 1) *
            (rothKronecker D P *
              rothKronecker D (MvPolynomial.pderiv h (MvPolynomial.X n)))) =
        C (D ^ (n : ℕ) : K) * X ^ (D ^ (n : ℕ) - 1) *
          rothKronecker D P := by
      rw [Finset.sum_eq_single n]
      ·
        simp [mul_assoc, mul_comm]
      ·
        intro h _ hne
        rw [MvPolynomial.pderiv_X_of_ne hne.symm]
        simp
      ·
        simp
    rw [map_mul, rothKronecker_X_h, derivative_mul, hP, derivative_X_pow]
    symm
    calc
      _ = ∑ h : Fin m,
            (C (D ^ (h : ℕ) : K) * X ^ (D ^ (h : ℕ) - 1) *
                rothKronecker D (MvPolynomial.pderiv h P) *
                  X ^ D ^ (n : ℕ) +
              C (D ^ (h : ℕ) : K) * X ^ (D ^ (h : ℕ) - 1) *
                (rothKronecker D P *
                  rothKronecker D (MvPolynomial.pderiv h (MvPolynomial.X n)))) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [MvPolynomial.pderiv_mul]
        simp only [map_add, map_mul, rothKronecker_X_h]
        ring
      _ = (∑ h : Fin m,
              C (D ^ (h : ℕ) : K) * X ^ (D ^ (h : ℕ) - 1) *
                rothKronecker D (MvPolynomial.pderiv h P) *
                  X ^ D ^ (n : ℕ)) +
            ∑ h : Fin m,
              C (D ^ (h : ℕ) : K) * X ^ (D ^ (h : ℕ) - 1) *
                (rothKronecker D P *
                  rothKronecker D (MvPolynomial.pderiv h (MvPolynomial.X n))) :=
        Finset.sum_add_distrib
      _ = (∑ h : Fin m,
              C (D ^ (h : ℕ) : K) * X ^ (D ^ (h : ℕ) - 1) *
                rothKronecker D (MvPolynomial.pderiv h P)) *
              X ^ D ^ (n : ℕ) +
            C (D ^ (n : ℕ) : K) * X ^ (D ^ (n : ℕ) - 1) *
              rothKronecker D P := by
        rw [← Finset.sum_mul, hsecond]
      _ = _ := by
        push_cast
        ring

private lemma rothMvHasse_single_one_h
  {m : ℕ}
  (h : Fin m)
  (P : MvPolynomial (Fin m) ℚ) :
  rothMvHasse (Finsupp.single h 1) P = MvPolynomial.pderiv h P := by
  ext i
  rw [rothMvHasse_coeff_h, MvPolynomial.coeff_pderiv]
  have hprod :
    (Finset.univ.prod fun b : Fin m =>
          (Nat.choose ((i + (Finsupp.single h 1 : RothMvIndex m)) b)
            ((Finsupp.single h 1 : RothMvIndex m) b) : ℚ)) =
        (i h + 1 : ℚ) := by
    rw [Finset.prod_eq_single h]
    ·
      simp
    ·
      intro b _ hbh
      simp [hbh]
    ·
      simp
  rw [hprod]
  ring

private lemma roth_choose_comp_h
  (l i j : ℕ) :
  (l + j).choose j * (l + j + i).choose i =
    (i + j).choose i * (l + (i + j)).choose (i + j) := by
  have h := Nat.choose_mul (n := l + j + i) (k := i + j) (s := i)
    (Nat.le_add_right i j)
  have hsub : l + j + i - i = l + j := by omega
  rw [hsub] at h
  have hk : i + j - i = j := by omega
  rw [hk] at h
  have htotal : l + j + i = l + (i + j) := by omega
  rw [htotal] at h
  rw [htotal]
  simpa only [mul_comm] using h.symm

private lemma rothMvHasse_comp_h
  {m : ℕ} {R : Type*} [CommSemiring R]
  (P : MvPolynomial (Fin m) R)
  (i j : RothMvIndex m) :
  rothMvHasse j (rothMvHasse i P) =
    (Finset.univ.prod fun h => (Nat.choose ((i + j) h) (i h) : R)) •
      rothMvHasse (i + j) P := by
  ext l
  rw [rothMvHasse_coeff_h, rothMvHasse_coeff_h]
  rw [MvPolynomial.coeff_smul, rothMvHasse_coeff_h]
  rw [smul_eq_mul]
  have hprod :
    (Finset.univ.prod fun h => (Nat.choose ((l + j) h) (j h) : R)) *
          (Finset.univ.prod fun h => (Nat.choose ((l + j + i) h) (i h) : R)) =
        (Finset.univ.prod fun h => (Nat.choose ((i + j) h) (i h) : R)) *
          (Finset.univ.prod fun h =>
            (Nat.choose ((l + (i + j)) h) ((i + j) h) : R)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro h _
    simp only [Finsupp.add_apply]
    rw [← Nat.cast_mul, ← Nat.cast_mul, roth_choose_comp_h]
  have hindex : l + j + i = l + (i + j) := by
    ext h
    simp only [Finsupp.add_apply]
    omega
  rw [hindex] at hprod
  rw [hindex, ← mul_assoc, ← mul_assoc, hprod]

private lemma roth_pderiv_hasse_h
  {m : ℕ}
  (h : Fin m)
  (i : RothMvIndex m)
  (P : MvPolynomial (Fin m) ℚ) :
  MvPolynomial.pderiv h (rothMvHasse i P) =
    (i h + 1 : ℚ) • rothMvHasse (i + Finsupp.single h 1) P := by
  rw [← rothMvHasse_single_one_h, rothMvHasse_comp_h]
  have hprod :
    (Finset.univ.prod fun b : Fin m =>
          (Nat.choose ((i + (Finsupp.single h 1 : RothMvIndex m)) b) (i b) : ℚ)) =
        (i h + 1 : ℚ) := by
    rw [Finset.prod_eq_single h]
    ·
      simp
    ·
      intro b _ hbh
      simp [hbh]
    ·
      simp
  rw [hprod]

private lemma rothMvOrder_add_single_one_h
  {m : ℕ}
  (i : RothMvIndex m)
  (h : Fin m) :
  rothMvOrder (i + Finsupp.single h 1) = rothMvOrder i + 1 := by
  simp [rothMvOrder, Finset.sum_add_distrib]

private lemma rothKronHasseJetRows_mono_h
  {m k : ℕ}
  (D : ℕ)
  (f : Fin k → MvPolynomial (Fin m) ℚ)
  {s t : ℕ}
-- given
  (hst : s ≤ t) :
-- imply
  rothKronHasseJetRows D f s ⊆ rothKronHasseJetRows D f t := by
-- proof
  rintro v ⟨i, hi, rfl⟩
  refine ⟨i, hi.trans hst, rfl⟩

private lemma rothKronHasseRow_derivative_h
  {m k : ℕ}
  (D : ℕ)
  (f : Fin k → MvPolynomial (Fin m) ℚ)
  (i : RothMvIndex m) :
  rothPolyRowDerivative (rothKronHasseRow D f i) =
    Finset.univ.sum fun h : Fin m =>
      (C (D ^ (h : ℕ) : ℚ) * X ^ (D ^ (h : ℕ) - 1) * C (i h + 1 : ℚ)) •
        rothKronHasseRow D f (i + Finsupp.single h 1) := by
  funext j
  simp only [rothPolyRowDerivative, rothKronHasseRow, Pi.smul_apply,
    Finset.sum_apply]
  rw [rothKronecker_derivative_h]
  apply Finset.sum_congr rfl
  intro h _
  rw [roth_pderiv_hasse_h]
  simp only [Algebra.smul_def, map_mul]
  simp [rothKronecker]
  ring

/--
[rothKronHasseRowDerivative_mem_span](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]

private lemma main
  {m k : ℕ}
  (D : ℕ)
  (f : Fin k → MvPolynomial (Fin m) ℚ)
  {s : ℕ}
  {v : Fin k → ℚ[X]}
-- given
  (hv : v ∈ Submodule.span ℚ[X] (rothKronHasseJetRows D f s)) :
-- imply
  rothPolyRowDerivative v ∈
    Submodule.span ℚ[X] (rothKronHasseJetRows D f (s + 1)) := by
-- proof
  let T := Submodule.span ℚ[X] (rothKronHasseJetRows D f (s + 1))
  have hold : Submodule.span ℚ[X] (rothKronHasseJetRows D f s) ≤ T :=
    Submodule.span_mono (rothKronHasseJetRows_mono_h D f (Nat.le_succ s))
  apply Submodule.span_induction (R := ℚ[X]) (s := rothKronHasseJetRows D f s)
    (p := fun v _ ↦ rothPolyRowDerivative v ∈ T)
  ·
    rintro _ ⟨i, hi, rfl⟩
    rw [rothKronHasseRow_derivative_h]
    apply Submodule.sum_mem
    intro h _
    apply T.smul_mem
    apply Submodule.subset_span
    refine ⟨i + Finsupp.single h 1, ?_, rfl⟩
    rw [rothMvOrder_add_single_one_h]
    omega
  ·
    have hz : rothPolyRowDerivative (0 : Fin k → ℚ[X]) = 0 := by
      ext j
      simp [rothPolyRowDerivative]
    rw [hz]
    apply T.zero_mem
  ·
    intro u w _ _ hu hw
    have hadd : rothPolyRowDerivative (u + w) =
      rothPolyRowDerivative u + rothPolyRowDerivative w := by
      ext j
      simp [rothPolyRowDerivative]
    rw [hadd]
    apply T.add_mem hu hw
  ·
    intro c w hw hw'
    have hwT : w ∈ T := hold hw
    have hsum : derivative c • w + c • rothPolyRowDerivative w ∈ T :=
      T.add_mem (T.smul_mem _ hwT) (T.smul_mem _ hw')
    convert hsum using 1
    ext j
    simp [rothPolyRowDerivative, derivative_mul]
  ·
    apply hv


-- created on 2026-10-21
