/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/SylvesterInertia.lean -/


import Mathlib.Analysis.Matrix.PosDef
import Lemma.Matrix.SylvesterInertia

-- A concrete indefinite congruence has one positive and one negative eigenvalue.
example :
    let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, -1]
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]
    let B := P.transpose * A * P
    ∃ hB : B.IsHermitian,
      (Finset.univ.filter (fun i => 0 < hB.eigenvalues i)).card = 1 ∧
      (Finset.univ.filter (fun i => hB.eigenvalues i < 0)).card = 1 ∧
      (Finset.univ.filter (fun i => hB.eigenvalues i = 0)).card = 0 := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, -1]
  let P : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]
  let B := P.transpose * A * P
  change ∃ hB : B.IsHermitian,
    (Finset.univ.filter (fun i => 0 < hB.eigenvalues i)).card = 1 ∧
    (Finset.univ.filter (fun i => hB.eigenvalues i < 0)).card = 1 ∧
    (Finset.univ.filter (fun i => hB.eigenvalues i = 0)).card = 0
  have hA : A.IsHermitian := by
    exact Matrix.isHermitian_diagonal _
  have hBmatrix : B = !![1, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, B, P, Matrix.mul_apply]
  have hB : B.IsHermitian := by
    rw [hBmatrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.conjTranspose_apply]
  have hP : IsUnit P.det := by
    rw [isUnit_iff_ne_zero]
    norm_num [P, Matrix.det_fin_two]
  refine ⟨hB, ?_⟩
  have hprod :
      hA.eigenvalues 0 * hA.eigenvalues 1 = -1 := by
    calc
      _ = A.det := by
        rw [hA.det_eq_prod_eigenvalues, Fin.prod_univ_two]
        norm_num
      _ = -1 := by
        norm_num [A, Matrix.det_fin_two]
  have hsigns :
      (0 < hA.eigenvalues 0 ∧ hA.eigenvalues 1 < 0) ∨
      (hA.eigenvalues 0 < 0 ∧ 0 < hA.eigenvalues 1) := by
    apply mul_neg_iff.mp
    nlinarith [hprod]
  have hAcounts :
      (Finset.univ.filter (fun i => 0 < hA.eigenvalues i)).card = 1 ∧
      (Finset.univ.filter (fun i => hA.eigenvalues i < 0)).card = 1 ∧
      (Finset.univ.filter (fun i => hA.eigenvalues i = 0)).card = 0 := by
    rcases hsigns with ⟨h0pos, h1neg⟩ | ⟨h0neg, h1pos⟩
    · have hpos : Finset.univ.filter (fun i => 0 < hA.eigenvalues i) = {0} := by
        ext i
        fin_cases i <;> simp [h0pos, not_lt_of_ge h1neg.le]
      have hneg : Finset.univ.filter (fun i => hA.eigenvalues i < 0) = {1} := by
        ext i
        fin_cases i <;> simp [not_lt_of_ge h0pos.le, h1neg]
      have hzero : Finset.univ.filter (fun i => hA.eigenvalues i = 0) = ∅ := by
        ext i
        fin_cases i <;> simp [h0pos.ne', h1neg.ne]
      simp [hpos, hneg, hzero]
    · have hpos : Finset.univ.filter (fun i => 0 < hA.eigenvalues i) = {1} := by
        ext i
        fin_cases i <;> simp [not_lt_of_ge h0neg.le, h1pos]
      have hneg : Finset.univ.filter (fun i => hA.eigenvalues i < 0) = {0} := by
        ext i
        fin_cases i <;> simp [h0neg, not_lt_of_ge h1pos.le]
      have hzero : Finset.univ.filter (fun i => hA.eigenvalues i = 0) = ∅ := by
        ext i
        fin_cases i <;> simp [h0neg.ne, h1pos.ne']
      simp [hpos, hneg, hzero]
  have hinertia :=
    MetaMathlibExt.sylvester_law_of_inertia hA hB P hP rfl
  exact ⟨hinertia.1.symm.trans hAcounts.1,
    hinertia.2.1.symm.trans hAcounts.2.1,
    hinertia.2.2.symm.trans hAcounts.2.2⟩

-- Congruence transports positivity of every eigenvalue.
example {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (P : Matrix n n ℝ) (hP : IsUnit P.det)
    (hcong : B = P.transpose * A * P)
    (hpositive : ∀ i, 0 < hA.eigenvalues i) :
    ∀ i, 0 < hB.eigenvalues i := by
  have hcounts :=
    MetaMathlibExt.sylvester_law_of_inertia hA hB P hP hcong
  have hcardA :
      (Finset.univ.filter (fun i => 0 < hA.eigenvalues i)).card =
        Fintype.card n := by
    rw [Finset.card_eq_iff_eq_univ]
    exact Finset.filter_eq_self.mpr fun i _ => hpositive i
  have hcardB :
      (Finset.univ.filter (fun i => 0 < hB.eigenvalues i)).card =
        Fintype.card n := by
    calc
      _ = (Finset.univ.filter (fun i => 0 < hA.eigenvalues i)).card :=
        hcounts.1.symm
      _ = Fintype.card n := hcardA
  have hfilterB :
      Finset.univ.filter (fun i => 0 < hB.eigenvalues i) = Finset.univ :=
    Finset.eq_univ_of_card _ hcardB
  intro i
  have hi : i ∈ Finset.univ.filter (fun j => 0 < hB.eigenvalues j) := by
    rw [hfilterB]
    exact Finset.mem_univ i
  exact (Finset.mem_filter.mp hi).2
