/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/Paving.lean -/

import Def.Analysis.CStarAlgebra.KadisonSinger.Paving
import Lemma.Complex.CStarAlgebra.KadisonSinger.Paving
import Def.MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

noncomputable section

universe v

-- Anderson paving specializes the universe-polymorphic MSS bound to its `Fin` indices.
example (hMSS : FiniteMSSBound.{0}) {n r : ℕ} (hr : 0 < r)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hdiagA : ∀ i, A i i = 0) (hnormA : ‖A‖ ≤ 1) :
    ∃ c : Fin n → Fin (r * r), ∀ j,
      ‖Matrix.diagonal (fun i ↦ if c i = j then (1 : ℂ) else 0) * A *
        Matrix.diagonal (fun i ↦ if c i = j then (1 : ℂ) else 0)‖ ≤
          2 * (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 - 1 :=
  andersonPaving_of_finiteMSS hMSS hr A hA hdiagA hnormA

-- The MSS bound partitions a concrete one-vector Parseval frame into two colours.
example (hMSS : FiniteMSSBound.{0}) :
    ∃ c : Fin 1 → Fin 2, ∀ j,
      ‖((∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (unitFrame i) (star (unitFrame i))) :
          Matrix (Fin 1) (Fin 1) ℂ)‖ ≤
        (1 / Real.sqrt 2 + Real.sqrt 1) ^ 2 := by
  apply exists_frame_partition_of_finiteMSS hMSS (r := 2) (d := 1)
  · norm_num
  · norm_num
  · exact unitFrame_sum
  · exact unitFrame_norm

-- The finite MSS bound paves the nonzero Pauli matrix at two base colours.
example (hMSS : FiniteMSSBound.{0}) :
    ∃ c : Fin 2 → Fin (2 * 2), ∀ j,
      ‖Matrix.diagonal (fun i ↦ if c i = j then (1 : ℂ) else 0) * pauliX *
        Matrix.diagonal (fun i ↦ if c i = j then (1 : ℂ) else 0)‖ ≤
          2 * (1 / Real.sqrt 2 + Real.sqrt (1 / 2 : ℝ)) ^ 2 - 1 := by
  exact andersonPaving_of_finiteMSS hMSS (r := 2) (by norm_num) pauliX
    pauliX_isHermitian pauliX_diagonal pauliX_norm_le_one

end
end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving
