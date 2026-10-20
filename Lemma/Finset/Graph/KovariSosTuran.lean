import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Graph.KovariSosTuran
open Finset Fintype
open MetaMathlibExt


/--
[kovari_sos_turan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/KovariSosTuran.lean)
-/
@[path]
private lemma kovari_sos_turan_eq
  {m n s t : ℕ}
-- given
  (ht : 0 < t)
  (hs : 1 ≤ s)
  (htn : t ≤ n) :
-- imply
  (SimpleGraph.zarankiewicz m n s t : ℝ) ≤
    Real.rpow ((s : ℝ) - 1) (1 / (t : ℝ)) * ((n : ℝ) - (t : ℝ) + 1) *
    Real.rpow (m : ℝ) (1 - 1 / (t : ℝ)) + ((t : ℝ) - 1) * (m : ℝ) := by
-- proof
  apply MetaMathlibExt.kovari_sos_turan m n s t ht hs htn


-- created on 2026-10-20
