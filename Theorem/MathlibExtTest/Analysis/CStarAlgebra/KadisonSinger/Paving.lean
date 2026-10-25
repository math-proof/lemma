/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/Paving.lean -/

import Def.Analysis.CStarAlgebra.KadisonSinger.Paving
import Lemma.Complex.CStarAlgebra.KadisonSinger.Paving
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

noncomputable section

universe v

-- Frame partitions accept frame indices in an independent universe.
example (hMSS : FiniteMSSBound.{0}) {I : Type v} [Fintype I] {d r : ℕ}
    (hr : 0 < r) (frame : I → Fin d → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hframe : ∑ i, Matrix.vecMulVec (frame i) (star (frame i)) = 1)
    (hframeNorm : ∀ i, ∑ k, ‖frame i k‖ ^ 2 ≤ δ) :
    ∃ c : I → Fin r, ∀ j,
      ‖((∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (frame i) (star (frame i))) : Matrix (Fin d) (Fin d) ℂ)‖ ≤
          (1 / Real.sqrt r + Real.sqrt δ) ^ 2 :=
  exists_frame_partition_of_finiteMSS hMSS hr frame δ hδ hframe hframeNorm

end
end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving
