import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing


/--
[smooth_iff_cotangent_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec19Prop32SmoothCompletion.lean)
-/
@[path]
lemma smooth_iff_cotangent_dim
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  IsRegularLocalRing R ↔ ↑(Module.finrank (ResidueField R) (CotangentSpace R)) = ringKrullDim R :=
-- proof
  IsRegularLocalRing.iff_finrank_cotangentSpace R

/--
[smooth_iff_cotangent_dim_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec19Prop32SmoothCompletion.lean)
-/
@[path]
lemma smooth_iff_cotangent_dim_nat
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R]
  {d : ℕ}
-- given
  (hdim : ringKrullDim R = d) :
-- imply
  IsRegularLocalRing R ↔ Module.finrank (ResidueField R) (CotangentSpace R) = d := by
-- proof
  rw [IsRegularLocalRing.iff_finrank_cotangentSpace, hdim, Nat.cast_inj]


-- created on 2026-10-23
