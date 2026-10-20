import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.CoveringSystem
open Pointwise
open CoveringSystem
open Int


/--
[iUnion_cosets](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CoveringSystem.lean)
-/
@[path]
private lemma iUnion_cosets_eq
  [CommSemiring R]
  {c : CoveringSystem R} :
-- imply
  ⋃ i, c.coset i = Set.univ := by
-- proof
  apply CoveringSystem.iUnion_cosets c

/--
[indexedCoveringClasses_isCoveringSystem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CoveringSystem.lean)
-/
@[path]
private lemma indexedCoveringClasses_isCoveringSystem_iff_eq
  {k : ℕ}
  {moduli : Fin k → ℕ}
  {residues : Fin k → ℤ} :
-- imply
  IsCoveringSystem (indexedCoveringClasses moduli residues) ↔
      ∀ z : ℤ, ∃ i, z ≡ residues i [ZMOD (moduli i : ℤ)] := by
-- proof
  apply Int.indexedCoveringClasses_isCoveringSystem_iff moduli residues


-- created on 2026-10-20
