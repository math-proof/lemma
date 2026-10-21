import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.RothPolyJetRows.sub.RothPolyJetRows.of.Le
import Lemma.Polynomial.RothPolyRowDerivative_RothPolyDerivativeRow.eq.RothPolyDerivativeRowAdd_1
import Lemma.Polynomial.RothPolyWronskianDerivativeRow0.eq.Zero
import Lemma.Polynomial.LinearIndependent_J.of.LinearIndependent
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


private lemma exists_row_det_ne_zero_of_mem_span
  {k : ℕ} [CommRing K]
  (A : Matrix (Fin k) (Fin k) K)
  (i : Fin k)
  (S : Set (Fin k → K))
-- given
  (hA : A.det ≠ 0)
  (hi : A i ∈ Submodule.span K S) :
-- imply
  ∃ v ∈ S, (A.updateRow i v).det ≠ 0 := by
-- proof
  classical
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hall : ∀ v ∈ Submodule.span K S, (A.updateRow i v).det = 0 := by
    intro v hv
    apply Submodule.span_induction (R := K) (s := S)
      (p := fun v _ ↦ (A.updateRow i v).det = 0)
    ·
      intro v hv
      apply h v hv
    ·
      apply Matrix.det_eq_zero_of_row_eq_zero i
      intro j
      simp [Matrix.updateRow_apply]
    ·
      intro u v _ _ hu hv
      rw [Matrix.det_updateRow_add, hu, hv, add_zero]
    ·
      intro c v _ hv
      rw [Matrix.det_updateRow_smul, hv, mul_zero]
    ·
      apply hv
  have := hall (A i) hi
  rw [Matrix.updateRow_eq_self] at this
  apply hA this

private lemma exists_nonsingular_rows_of_mem_span
  {k : ℕ} [CommRing K]
  (A : Matrix (Fin k) (Fin k) K)
  (S : Fin k → Set (Fin k → K))
-- given
  (hA : A.det ≠ 0)
  (hspan : ∀ i, A i ∈ Submodule.span K (S i)) :
-- imply
  ∃ B : Matrix (Fin k) (Fin k) K, B.det ≠ 0 ∧ ∀ i, B i ∈ S i := by
-- proof
  classical
  have aux : ∀ s : Finset (Fin k),
      ∃ B : Matrix (Fin k) (Fin k) K, B.det ≠ 0 ∧
        (∀ i ∈ s, B i ∈ S i) ∧ (∀ i ∉ s, B i = A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨A, hA, ?_, ?_⟩
      · simp
      · simp
    | @insert i s his ih =>
      obtain ⟨B, hB, hBs, hBout⟩ := ih
      have hBi : B i ∈ Submodule.span K (S i) := by
        rw [hBout i his]
        apply hspan i
      obtain ⟨v, hv, hBv⟩ :=
        exists_row_det_ne_zero_of_mem_span B i (S i) hB hBi
      refine ⟨B.updateRow i v, hBv, ?_, ?_⟩
      ·
        intro j hj
        obtain rfl | hjs := Finset.mem_insert.mp hj
        · simpa using hv
        ·
          have hji : j ≠ i := by
            intro hji
            subst j
            apply his hjs
          rw [Matrix.updateRow_ne hji]
          apply hBs j hjs
      ·
        intro j hj
        have hji : j ≠ i := by
          intro hji
          subst j
          apply hj (Finset.mem_insert_self i s)
        rw [Matrix.updateRow_ne hji]
        apply hBout j (fun hjs ↦ hj (Finset.mem_insert_of_mem hjs))
  obtain ⟨B, hB, hrows, _⟩ := aux Finset.univ
  refine ⟨B, hB, ?_⟩
  intro i
  apply hrows i (Finset.mem_univ i)

private lemma rowDerivative_mem_span
  {k : ℕ} [Field K]
  (f : Fin k → K[X])
  {s : ℕ}
  {v : Fin k → K[X]}
-- given
  (hv : v ∈ Submodule.span K[X] (rothPolyJetRows f s)) :
-- imply
  rothPolyRowDerivative v ∈ Submodule.span K[X] (rothPolyJetRows f (s + 1)) := by
-- proof
  let T := Submodule.span K[X] (rothPolyJetRows f (s + 1))
  have hold : Submodule.span K[X] (rothPolyJetRows f s) ≤ T :=
    Submodule.span_mono (RothPolyJetRows.sub.RothPolyJetRows.of.Le f (Nat.le_succ s))
  apply Submodule.span_induction (R := K[X]) (s := rothPolyJetRows f s)
    (p := fun v _ ↦ rothPolyRowDerivative v ∈ T)
  ·
    rintro _ ⟨n, hn, rfl⟩
    rw [RothPolyRowDerivative_RothPolyDerivativeRow.eq.RothPolyDerivativeRowAdd_1]
    apply Submodule.subset_span
    refine ⟨n + 1, Nat.add_le_add_right hn 1, rfl⟩
  ·
    have hz : rothPolyRowDerivative (0 : Fin k → K[X]) = 0 := by
      ext j
      simp [rothPolyRowDerivative]
    rw [hz]
    apply T.zero_mem
  ·
    intro u w _ _ hu' hw'
    have hadd : rothPolyRowDerivative (u + w) =
        rothPolyRowDerivative u + rothPolyRowDerivative w := by
      ext j
      simp [rothPolyRowDerivative]
    rw [hadd]
    apply T.add_mem hu' hw'
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

private lemma wronskianRow_mem_span
  {k : ℕ} [Field K]
  (f : Fin (k + 1) → K[X]) :
    rothPolyWronskianRow f ∈ Submodule.span K[X] (rothPolyJetRows f 1) := by
  have h0 : rothPolyDerivativeRow f 0 ∈
    Submodule.span K[X] (rothPolyJetRows f 1) :=
    Submodule.subset_span ⟨0, by omega, rfl⟩
  have h1 : rothPolyDerivativeRow f 1 ∈
    Submodule.span K[X] (rothPolyJetRows f 1) :=
    Submodule.subset_span ⟨1, le_rfl, rfl⟩
  have hmem := (Submodule.span K[X] (rothPolyJetRows f 1)).sub_mem
    ((Submodule.span K[X] (rothPolyJetRows f 1)).smul_mem (f 0) h1)
    ((Submodule.span K[X] (rothPolyJetRows f 1)).smul_mem (f 0).derivative h0)
  convert hmem using 1
  ext j
  simp [rothPolyWronskianRow, rothPolyDerivativeRow, wronskian]

private lemma wronskianDerivativeRow_mem_span
  {k : ℕ} [Field K]
  (f : Fin (k + 1) → K[X])
  (n : ℕ) :
    rothPolyWronskianDerivativeRow f n ∈
      Submodule.span K[X] (rothPolyJetRows f (n + 1)) := by
  induction n with
  | zero =>
    change rothPolyWronskianRow f ∈ Submodule.span K[X] (rothPolyJetRows f 1)
    apply wronskianRow_mem_span f
  | succ n ih =>
    have hder := rowDerivative_mem_span f ih
    convert hder using 1
    ·
      ext j
      simp only [rothPolyRowDerivative, rothPolyWronskianDerivativeRow]
      rw [Function.iterate_succ_apply']

private lemma exists_poly_adapted_matrix
  [Field K] [CharZero K] :
    ∀ {k : ℕ} (f : Fin k → K[X]), LinearIndependent K f →
      ∃ A : Matrix (Fin k) (Fin k) K[X], A.det ≠ 0 ∧
        ∀ s : Fin k, A s ∈ Submodule.span K[X] (rothPolyJetRows f s) := by
  intro k
  induction k with
  | zero =>
    intro f _
    refine ⟨0, by simp, ?_⟩
    intro s
    apply Fin.elim0 s
  | succ k ih =>
    intro f hf
    let g : Fin k → K[X] :=
      fun j ↦ wronskian (f 0) (f j.succ)
    have hg : LinearIndependent K g :=
      LinearIndependent_J.of.LinearIndependent f hf
    obtain ⟨A, hA, hArows⟩ := ih g hg
    let B : Matrix (Fin (k + 1)) (Fin (k + 1)) K[X] :=
      Fin.cases f (fun s ↦ Fin.cons 0 (A s))
    have hBdet : B.det = f 0 * A.det := by
      rw [Matrix.det_succ_column_zero]
      rw [Fin.sum_univ_succ]
      simp [B, Matrix.submatrix, hf.ne_zero 0]
      rfl
    have hB : B.det ≠ 0 := by
      rw [hBdet]
      apply mul_ne_zero (hf.ne_zero 0) hA
    refine ⟨B, hB, ?_⟩
    intro s
    refine Fin.cases ?_ (fun t ↦ ?_) s
    ·
      change f ∈ Submodule.span K[X] (rothPolyJetRows f 0)
      apply Submodule.subset_span
      refine ⟨0, le_rfl, ?_⟩
      ext j
      simp [rothPolyDerivativeRow]
    ·
      change Fin.cons 0 (A t) ∈
        Submodule.span K[X] (rothPolyJetRows f t.succ)
      let T := Submodule.span K[X] (rothPolyJetRows f t.succ)
      apply Submodule.span_induction (R := K[X]) (s := rothPolyJetRows g t)
        (p := fun v _ ↦ Fin.cons 0 v ∈ T)
      ·
        rintro _ ⟨n, hn, rfl⟩
        have heq : Fin.cons 0 (rothPolyDerivativeRow g n) =
            rothPolyWronskianDerivativeRow f n := by
          ext j
          refine Fin.cases ?_ (fun u ↦ ?_) j
          · simp [RothPolyWronskianDerivativeRow0.eq.Zero]
          · simp [rothPolyDerivativeRow, rothPolyWronskianDerivativeRow, g]
        rw [heq]
        apply Submodule.span_mono
          (RothPolyJetRows.sub.RothPolyJetRows.of.Le f (Nat.add_le_add_right hn 1))
          (wronskianDerivativeRow_mem_span f n)
      ·
        have hz : (Fin.cons (0 : K[X]) (0 : Fin k → K[X]) :
            Fin (k + 1) → K[X]) = 0 := by
          ext j
          refine Fin.cases (by simp) (fun w ↦ by simp) j
        rw [hz]
        apply T.zero_mem
      ·
        intro u v _ _ hu hv
        have hadd : (Fin.cons (0 : K[X]) (u + v) : Fin (k + 1) → K[X]) =
            Fin.cons 0 u + Fin.cons 0 v := by
          ext j
          refine Fin.cases (by simp) (fun w ↦ by simp) j
        rw [hadd]
        apply T.add_mem hu hv
      ·
        intro c v _ hv
        have hsmul : (Fin.cons (0 : K[X]) (c • v) : Fin (k + 1) → K[X]) =
            c • Fin.cons 0 v := by
          ext j
          refine Fin.cases (by simp) (fun w ↦ by simp) j
        rw [hsmul]
        apply T.smul_mem c hv
      ·
        apply hArows t

/--
[roth_exists_poly_wronskian_orders](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {k : ℕ} [Field K] [CharZero K]
  (f : Fin k → K[X])
-- given
  (hf : LinearIndependent K f) :
-- imply
  ∃ n : Fin k → ℕ, (∀ s, n s ≤ s) ∧
    (Matrix.det fun s j ↦ (derivative^[(n s)]) (f j)) ≠ 0 := by
-- proof
  classical
  obtain ⟨A, hA, hArows⟩ := exists_poly_adapted_matrix f hf
  obtain ⟨B, hB, hBrows⟩ :=
    exists_nonsingular_rows_of_mem_span A (fun s ↦ rothPolyJetRows f s)
      hA hArows
  choose n hn hrow using hBrows
  refine ⟨n, hn, ?_⟩
  have hBeq : B = fun s j ↦ (derivative^[(n s)]) (f j) := by
    ext s j
    rw [hrow s]
    rfl
  rwa [← hBeq]


-- created on 2026-10-21
