import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.TangentSpaceDim
open IsLocalRing Module


/--
[tangentDim_ge_krullDim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TangentSpaceDim.lean)
-/
@[path]
lemma tangentDim_ge_krullDim
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  ringKrullDim R ≤ ↑(finrank (ResidueField R) (CotangentSpace R)) := by
-- proof
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact ringKrullDim_le_spanFinrank_maximalIdeal R

/--
[smooth_iff_tangentDim_eq_krullDim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TangentSpaceDim.lean)
-/
@[path]
lemma smooth_iff_tangentDim_eq_krullDim
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  IsRegularLocalRing R ↔ ↑(finrank (ResidueField R) (CotangentSpace R)) = ringKrullDim R :=
-- proof
  IsRegularLocalRing.iff_finrank_cotangentSpace R

/--
[tangentDim_gt_krullDim_of_not_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TangentSpaceDim.lean)
-/
@[path]
lemma tangentDim_gt_krullDim_of_not_smooth
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R]
-- given
  (h : ¬IsRegularLocalRing R) :
-- imply
  ringKrullDim R < ↑(finrank (ResidueField R) (CotangentSpace R)) := by
-- proof
  rw [lt_iff_le_and_ne]
  exact ⟨tangentDim_ge_krullDim R,
    fun heq => h ((smooth_iff_tangentDim_eq_krullDim R).mpr heq.symm)⟩

/--
[tangentSpace_dim_characterizes_smoothness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TangentSpaceDim.lean)
-/
@[path]
lemma tangentSpace_dim_characterizes_smoothness
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  ringKrullDim R ≤ ↑(finrank (ResidueField R) (CotangentSpace R)) ∧ (IsRegularLocalRing R ↔ ↑(finrank (ResidueField R) (CotangentSpace R)) = ringKrullDim R) :=
-- proof
  ⟨tangentDim_ge_krullDim R, smooth_iff_tangentDim_eq_krullDim R⟩


-- created on 2026-10-23
