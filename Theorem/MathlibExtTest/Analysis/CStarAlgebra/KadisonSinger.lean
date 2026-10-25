/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger.lean -/

import Def.Analysis.CStarAlgebra.KadisonSinger
import Lemma.Real.CStarAlgebra.KadisonSinger
import Def.MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger
open scoped Matrix.Norms.L2Operator

open MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted


namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger

noncomputable section

-- The theorem gives a half-norm paving of the nonzero two-dimensional Pauli matrix.
example :
    ∃ (r : ℕ), 0 < r ∧ ∃ c : Fin 2 → Fin r, ∀ j,
      ‖pavingProj 2 r c j * pauliX * pavingProj 2 r c j‖ ≤ (1 / 2 : ℝ) := by
  obtain ⟨r, hr, hall⟩ := kadison_singer_paving (1 / 2) (by norm_num)
  obtain ⟨c, hc⟩ := hall 2 pauliX pauliX_isHermitian pauliX_diagonal
    pauliX_norm_le_one
  exact ⟨r, hr, c, hc⟩

end
end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger
