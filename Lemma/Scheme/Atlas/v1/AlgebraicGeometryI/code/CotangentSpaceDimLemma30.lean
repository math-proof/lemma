import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing


/--
[cotangentSpace_dim_ge_krullDim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CotangentSpaceDimLemma30.lean)
-/
@[path]
lemma cotangentSpace_dim_ge_krullDim
  {R : Type*}
  [CommRing R]
  [IsNoetherianRing R]
  [IsLocalRing R] :
-- imply
  ringKrullDim R ≤ Module.finrank (ResidueField R) (CotangentSpace R) := by
-- proof
  rw [← maximalIdeal_height_eq_ringKrullDim]
  have h := Ideal.height_le_spanFinrank (maximalIdeal R) (Ideal.IsPrime.ne_top')
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R] at h
  exact_mod_cast h


-- created on 2026-10-23
