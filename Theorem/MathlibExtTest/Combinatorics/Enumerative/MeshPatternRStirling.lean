/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MeshPatternRStirling.lean -/


import Def.Combinatorics.Enumerative.MeshPatternRStirling.Part3
import Lemma.Finset.Enumerative.MeshPatternRStirling
import Lemma.Finset.Enumerative.MeshPatternStirlingRecursion
import Theorem.Combinatorics.Enumerative.MeshPatternStirlingRecursion.Part3


namespace MetaMathlibExt

-- Decidability inference for the public mesh predicates.
example (r : ℕ) (σ : Equiv.Perm (Fin 3)) :
    DecidablePred (MatchPred r σ) := inferInstance

example (r : ℕ) (σ : Equiv.Perm (Fin 3)) :
    Decidable (ZeroPred r σ) := inferInstance

-- The canonical statistic unfolds to its filter-plus-correction form.
example (r : ℕ) {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    meshN r σ = (Finset.univ.filter (MatchPred r σ)).card +
      (if ZeroPred r σ then 1 else 0) := rfl

-- The canonical polynomial unfolds to its generating sum.
example (m r : ℕ) :
    PolyN m r =
      ∑ σ : Equiv.Perm (Fin m), (Polynomial.X : Polynomial ℕ) ^ meshN r σ := rfl

-- Concrete boundary values on `Fin 2`:
-- identity has no matches for `r = 2` but takes the zero correction.
example : meshN 2 (Equiv.refl (Fin 2)) = 1 := by decide

-- The transposition has no matches and no zero correction for `r = 2`.
example : meshN 2 (Equiv.swap (0 : Fin 2) 1) = 0 := by decide

-- For `r = 1` every left-to-right maximum matches; identity on `Fin 2`
-- has two, plus the zero correction.
example : meshN 1 (Equiv.refl (Fin 2)) = 3 := by decide

-- The public enumeration theorem applies at small values.
example : Fintype.card {σ : Equiv.Perm (Fin 2) // meshN 2 σ = 1} =
    (2 - 1).factorial * rStirlingFirst 2 (1 + 2 - 1) (2 - 1) :=
  meshPatternCount_eq_factorial_mul_rStirlingNumber_general 2 2 1 le_rfl le_rfl

end MetaMathlibExt
