import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.HyperbolicCancellation
import Lemma.Int.OrthogonalSum.eq.Add
import Lemma.Submodule.Any_LeAndDisjointAndEq.of.Le
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.KernelDecomposition
open Formalization
open Garrett


/--
[isAlt_skew](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/BilinHermitianProps.lean)
-/
@[path]
private lemma main
  [Field k]
  [Invertible (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
  {x y : V}
-- given
  (hAlt : B.IsAlt) :
-- imply
  B x y = -(B y x) := by
-- proof
  have h1 := hAlt (x + y)
  simp only [map_add, LinearMap.add_apply] at h1
  rw [hAlt x, hAlt y, zero_add, add_zero] at h1
  rw [add_comm] at h1
  exact add_eq_zero_iff_eq_neg.mp h1



-- created on 2026-10-23
-- updated on 2026-10-24
