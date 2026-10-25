import Mathlib
import sympy.Basic
import Def.NumberTheory.RamificationInertia.MaximalUnramified
open IntermediateField


namespace IntermediateField

/--
[le_maximalUnramifiedSubextension](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/MaximalUnramified.lean)
-/
@[path]
lemma le_maximalUnramifiedSubextension
  [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  {E : IntermediateField K L}
-- given
  (hE : IsFiniteUnramified A E) :
-- imply
  E ≤ maximalUnramifiedSubextension A K L :=
-- proof
  le_iSup_of_le E (le_iSup_of_le hE le_rfl)

end IntermediateField

namespace IntermediateField

/--
[maximalUnramifiedSubextension_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/MaximalUnramified.lean)
-/
@[path]
lemma maximalUnramifiedSubextension_le_iff
  [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  {F : IntermediateField K L} :
-- imply
  maximalUnramifiedSubextension A K L ≤ F ↔
    ∀ E : IntermediateField K L, IsFiniteUnramified A E → E ≤ F := by
-- proof
  constructor
  · intro h E hE
    exact (le_maximalUnramifiedSubextension hE).trans h
  · intro h
    unfold maximalUnramifiedSubextension
    apply iSup_le
    intro E
    apply iSup_le
    intro hE
    exact h E hE

end IntermediateField

namespace IntermediateField

/--
[IsFiniteUnramified.map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/MaximalUnramified.lean)
-/
@[path]
lemma IsFiniteUnramified.map
  [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  {E : IntermediateField K L}
-- given
  (hE : IsFiniteUnramified A E)
  (σ : L ≃ₐ[K] L) :
-- imply
  IsFiniteUnramified A (E.map σ.toAlgHom) := by
-- proof
  obtain ⟨hfin, hunr⟩ := hE
  constructor
  · exact LinearEquiv.finiteDimensional
    (IntermediateField.intermediateFieldMap σ E).toLinearEquiv
  · let e : E ≃ₐ[A] E.map (σ : L →ₐ[K] L) :=
    (IntermediateField.intermediateFieldMap σ E).restrictScalars A
    exact Algebra.FormallyUnramified.of_equiv e.mapIntegralClosure

end IntermediateField

namespace IntermediateField

variable {A K L : Type*} [CommRing A] [Field K] [Field L]
variable [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
/--
[map_maximalUnramifiedSubextension_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/MaximalUnramified.lean)
-/
@[path]
private lemma map_maximalUnramifiedSubextension_le (σ : L ≃ₐ[K] L) :
  (maximalUnramifiedSubextension A K L).map σ.toAlgHom ≤
    maximalUnramifiedSubextension A K L := by
  unfold maximalUnramifiedSubextension
  rw [IntermediateField.map_iSup]
  apply iSup_le
  intro E
  rw [IntermediateField.map_iSup]
  apply iSup_le
  intro hE
  exact le_maximalUnramifiedSubextension (hE.map σ)

end IntermediateField

namespace IntermediateField

/--
[map_maximalUnramifiedSubextension](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/MaximalUnramified.lean)
-/
@[path]
lemma map_maximalUnramifiedSubextension
  [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
-- given
  (σ : L ≃ₐ[K] L) :
-- imply
  (maximalUnramifiedSubextension A K L).map σ.toAlgHom =
    maximalUnramifiedSubextension A K L := by
-- proof
  apply le_antisymm
  · exact map_maximalUnramifiedSubextension_le σ
  · intro x hx
    rw [IntermediateField.mem_map]
    have hx' : σ.symm x ∈ maximalUnramifiedSubextension A K L := by
      apply map_maximalUnramifiedSubextension_le σ.symm
      rw [IntermediateField.mem_map]
      exact ⟨x, hx, by simp⟩
    exact ⟨σ.symm x, hx', by simp⟩

end IntermediateField


-- created on 2026-10-20
-- updated on 2026-10-23
