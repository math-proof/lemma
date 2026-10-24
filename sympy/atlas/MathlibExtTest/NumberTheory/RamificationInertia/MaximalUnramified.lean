/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/RamificationInertia/MaximalUnramified.lean -/


import sympy.atlas.NumberTheory.RamificationInertia.MaximalUnramified
import Lemma.Nat.RamificationInertia.MaximalUnramified


open IntermediateField

variable (A K L : Type*) [CommRing A] [Field K] [Field L]
variable [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

-- 1. `IsFiniteUnramified` unfolds to the finite-dimensional/formally-unramified conjunction.
example (E : IntermediateField K L) :
    IsFiniteUnramified A E ↔
      (FiniteDimensional K E ∧
        Algebra.FormallyUnramified A (integralClosure A E)) :=
  Iff.rfl

-- 2. A qualifying `E` lies below the maximal subextension.
example (E : IntermediateField K L) (hE : IsFiniteUnramified A E) :
    E ≤ maximalUnramifiedSubextension A K L :=
  le_maximalUnramifiedSubextension hE

-- 3. The `[simp]` universal-property iff for an arbitrary `F`.
example (F : IntermediateField K L) :
    maximalUnramifiedSubextension A K L ≤ F ↔
      ∀ E : IntermediateField K L, IsFiniteUnramified A E → E ≤ F :=
  maximalUnramifiedSubextension_le_iff

-- 4. Stability under a `K`-automorphism `σ` of `L`.
example (E : IntermediateField K L) (hE : IsFiniteUnramified A E)
    (σ : L ≃ₐ[K] L) :
    IsFiniteUnramified A (E.map σ.toAlgHom) :=
  hE.map σ

-- 5. Automorphism invariance of the maximal subextension.
example (σ : L ≃ₐ[K] L) :
    (maximalUnramifiedSubextension A K L).map σ.toAlgHom =
      maximalUnramifiedSubextension A K L :=
  map_maximalUnramifiedSubextension σ

-- 6. Definitional expansion to the double indexed supremum.
example :
    maximalUnramifiedSubextension A K L =
      ⨆ (E : IntermediateField K L) (_ : IsFiniteUnramified A E), E :=
  rfl
