import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.RingTheory.ConductorResidue
open MathlibExtTest MathlibExtTest.RingTheory MathlibExtTest.RingTheory.ConductorResidue


namespace MathlibExtTest.RingTheory.ConductorResidue

/--
[top_not_le_of_isMaximal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/ConductorResidue.lean)
-/
@[path]
lemma top_not_le_of_isMaximal
  [CommRing O]
  [CommRing B]
  [Algebra O B]
  {q : Ideal B}
  [q.IsMaximal]
  {c : Ideal B}
  [CommRing R]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hc : ¬ c ≤ q)
  (hclear : ∀ x ∈ c, ∀ b : B, ∃ o : O, algebraMap O B o = x * b) :
-- imply
  ¬(⊤ : Ideal R) ≤ p :=
-- proof
  fun h => (inferInstance : p.IsMaximal).ne_top (top_le_iff.mp h)

end MathlibExtTest.RingTheory.ConductorResidue

namespace MathlibExtTest.RingTheory.ConductorResidue

/--
[top_clears_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/ConductorResidue.lean)
-/
@[path]
lemma top_clears_identity
  [CommRing O]
  [CommRing B]
  [Algebra O B]
  {q : Ideal B}
  [q.IsMaximal]
  {c : Ideal B}
  [CommRing R]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hc : ¬ c ≤ q)
  (hclear : ∀ x ∈ c, ∀ b : B, ∃ o : O, algebraMap O B o = x * b) :
-- imply
  ∀ x ∈ (⊤ : Ideal R), ∀ b : R, ∃ o : R, algebraMap R R o = x * b := by
-- proof
  intro x _ b
  exact ⟨x * b, by simp⟩

end MathlibExtTest.RingTheory.ConductorResidue


-- created on 2026-10-23
