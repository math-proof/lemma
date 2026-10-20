import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RamificationInertia.MaximalUnramified
open IntermediateField


/--
[le_maximalUnramifiedSubextension](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/MaximalUnramified.lean)
-/
@[path]
private lemma le_maximalUnramifiedSubextension_eq
  [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  {E : IntermediateField K L}
-- given
  (hE : IsFiniteUnramified A E) :
-- imply
  E ≤ maximalUnramifiedSubextension A K L := by
-- proof
  apply IntermediateField.le_maximalUnramifiedSubextension hE

/--
[maximalUnramifiedSubextension_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/MaximalUnramified.lean)
-/
@[path]
private lemma maximalUnramifiedSubextension_le_iff_eq
  [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  {F : IntermediateField K L} :
-- imply
  maximalUnramifiedSubextension A K L ≤ F ↔
    ∀ E : IntermediateField K L, IsFiniteUnramified A E → E ≤ F := by
-- proof
  apply IntermediateField.maximalUnramifiedSubextension_le_iff

/--
[IsFiniteUnramified.map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/MaximalUnramified.lean)
-/
@[path]
private lemma IsFiniteUnramified_map_eq
  [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  {E : IntermediateField K L}
-- given
  (hE : IsFiniteUnramified A E)
  (σ : L ≃ₐ[K] L) :
-- imply
  IsFiniteUnramified A (E.map σ.toAlgHom) := by
-- proof
  apply IntermediateField.IsFiniteUnramified.map hE σ

/--
[map_maximalUnramifiedSubextension](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/MaximalUnramified.lean)
-/
@[path]
private lemma map_maximalUnramifiedSubextension_eq
  [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
-- given
  (σ : L ≃ₐ[K] L) :
-- imply
  (maximalUnramifiedSubextension A K L).map σ.toAlgHom =
    maximalUnramifiedSubextension A K L := by
-- proof
  apply IntermediateField.map_maximalUnramifiedSubextension σ


-- created on 2026-10-20
