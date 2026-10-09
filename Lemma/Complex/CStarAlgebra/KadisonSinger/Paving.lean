import Mathlib
import sympy.Basic
import sympy.Analysis.CStarAlgebra.KadisonSinger.Paving

open scoped BigOperators Matrix.Norms.L2Operator

/--
[exists_frame_partition_of_finiteMSS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/Paving.lean)
-/
@[path]
private lemma exists_frame_partition_of_finiteMSS_eq
-- given
  {I : Type*} [Fintype I] {d r : ℕ}
  (u : I → Fin d → ℂ) (δ : ℝ)
  (hMSS : Analysis.CStarAlgebra.KadisonSinger.FiniteMSSBound0) (hr : 0 < r) (hδ : 0 ≤ δ)
  (hframe : ∑ i, Matrix.vecMulVec (u i) (star (u i)) = 1)
  (hu : ∀ i, ∑ k, ‖u i k‖ ^ 2 ≤ δ) :
-- imply
  (∃ c : I → Fin r, ∀ j,
    ‖((∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
      Matrix.vecMulVec (u i) (star (u i))) : Matrix (Fin d) (Fin d) ℂ)‖ ≤
        (1 / Real.sqrt r + Real.sqrt δ) ^ 2) :=
-- proof
  Analysis.CStarAlgebra.KadisonSinger.exists_frame_partition_of_finiteMSS
    hMSS hr u δ hδ hframe hu

/--
[andersonPaving_of_finiteMSS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/Paving.lean)
-/
@[path]
private lemma andersonPaving_of_finiteMSS_eq
-- given
  {n r : ℕ}
  (A : Matrix (Fin n) (Fin n) ℂ)
  (hMSS : Analysis.CStarAlgebra.KadisonSinger.FiniteMSSBound0) (hr : 0 < r) (hA : A.IsHermitian)
  (hdiagA : ∀ i, A i i = 0) (hnormA : ‖A‖ ≤ 1) :
-- imply
  (∃ c : Fin n → Fin (r * r), ∀ j,
    ‖Matrix.diagonal (fun i ↦ if c i = j then (1 : ℂ) else 0) * A *
      Matrix.diagonal (fun i ↦ if c i = j then (1 : ℂ) else 0)‖ ≤
        2 * (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 - 1) :=
-- proof
  Analysis.CStarAlgebra.KadisonSinger.andersonPaving_of_finiteMSS
    hMSS hr A hA hdiagA hnormA


-- created on 2026-10-09
