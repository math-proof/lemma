import Mathlib
import sympy.Basic
open CategoryTheory


namespace AlgebraicGeometry

/--
[exists_maximal_extension_of_irreducible_separated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MaximalExtension.lean)
-/
@[path]
lemma exists_maximal_extension_of_irreducible_separated
  {X Y : Scheme.{u}}
  [IrreducibleSpace X]
  [IsReduced X]
  [Y.IsSeparated]
  {f : X.PartialMap Y} :
-- imply
  ∃ (g : X.PartialMap Y), g.equiv f ∧ (∀ (h : X.PartialMap Y), h.equiv f → h.domain ≤ g.domain) := by
-- proof
  refine ⟨f.toRationalMap.toPartialMap, ?_, ?_⟩
  · rw [← Scheme.PartialMap.toRationalMap_eq_iff]
    simp [Scheme.RationalMap.toRationalMap_toPartialMap]
  · intro h hequiv
    have htoRational : h.toRationalMap = f.toRationalMap :=
      Scheme.PartialMap.toRationalMap_eq_iff.mpr hequiv
    calc h.domain ≤ h.toRationalMap.domain := h.le_domain_toRationalMap
      _ = f.toRationalMap.domain := by rw [htoRational]
      _ = f.toRationalMap.toPartialMap.domain := rfl

end AlgebraicGeometry


-- created on 2026-10-23
