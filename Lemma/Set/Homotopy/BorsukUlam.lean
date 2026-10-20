import Mathlib
import sympy.Basic
import sympy.atlas.Topology.Homotopy.BorsukUlam
open Metric
open MathlibExt.Topology.Homotopy.BorsukUlamWanted


/--
[borsukUlam](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma borsukUlam_eq
  {n : ℕ}
  {f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n)}
-- given
  (hf : Continuous f) :
-- imply
  ∃ x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, f x = f (-x) := by
-- proof
  apply MathlibExt.Topology.Homotopy.BorsukUlamWanted.borsukUlam f hf


-- created on 2026-10-20
