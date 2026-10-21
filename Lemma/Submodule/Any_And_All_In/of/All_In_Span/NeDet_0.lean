import Mathlib
import sympy.Basic
import Lemma.Submodule.DetUpdateRow.ne.Zero.of.In_Span.NeDet_0
open Submodule


/--
[roth_exists_nonsingular_rows_of_mem_span](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
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
      ·
        intro i hi
        simp at hi
      ·
        intro i _
        rfl
    | @insert i s his ih =>
      obtain ⟨B, hB, hBs, hBout⟩ := ih
      have hBi : B i ∈ Submodule.span K (S i) := by
        rw [hBout i his]
        apply hspan i
      obtain ⟨v, hv, hBv⟩ :=
        DetUpdateRow.ne.Zero.of.In_Span.NeDet_0 B i (S i) hB hBi
      refine ⟨B.updateRow i v, hBv, ?_, ?_⟩
      ·
        intro j hj
        obtain rfl | hjs := Finset.mem_insert.mp hj
        ·
          simpa using hv
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
  refine ⟨B, hB, fun i ↦ hrows i (Finset.mem_univ i)⟩


-- created on 2026-10-21
