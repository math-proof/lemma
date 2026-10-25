import Mathlib
import sympy.Basic
import Def.NumberTheory.CoveringSystem
open Pointwise
open CoveringSystem
open Int


namespace CoveringSystem

/--
[iUnion_cosets](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CoveringSystem.lean)
-/
@[path]
lemma iUnion_cosets
  [CommSemiring R]
  {c : CoveringSystem R} :
-- imply
  ⋃ i, c.coset i = Set.univ :=
-- proof
  c.unionCovers
end CoveringSystem


namespace Int

/--
[indexedCoveringClasses_isCoveringSystem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CoveringSystem.lean)
-/
@[path]
lemma indexedCoveringClasses_isCoveringSystem_iff
  {k : ℕ}
  {moduli : Fin k → ℕ}
  {residues : Fin k → ℤ} :
-- imply
  IsCoveringSystem (indexedCoveringClasses moduli residues) ↔
      ∀ z : ℤ, ∃ i, z ≡ residues i [ZMOD (moduli i : ℤ)] := by
-- proof
  unfold IsCoveringSystem indexedCoveringClasses
  constructor
  · intro h z
    obtain ⟨c, hc, hcov⟩ := h z
    rw [Finset.mem_image] at hc
    obtain ⟨i, _, rfl⟩ := hc
    exact ⟨i, hcov⟩
  · intro h z
    obtain ⟨i, hi⟩ := h z
    exact ⟨(residues i, moduli i),
      Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩

end Int


-- created on 2026-10-20
-- updated on 2026-10-23
