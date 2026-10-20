import Mathlib
import sympy.Basic
import sympy.atlas.Topology.Continuum.PeanoCurve
open Topology
open MathlibExt.Topology.Continuum.PeanoCurveWanted


/--
[peano_curve_exists](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Continuum/PeanoCurve.lean)
-/
@[path]
private lemma peano_curve_exists_eq
  :
-- imply
  ∃ (f : C(unitInterval, unitInterval × unitInterval)), Function.Surjective f := by
-- proof
  apply MathlibExt.Topology.Continuum.PeanoCurveWanted.peano_curve_exists


-- created on 2026-10-20
