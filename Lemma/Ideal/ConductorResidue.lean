import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.ConductorResidue
open Ideal


namespace Ideal

/--
[quotient_coprime_residue_equiv_apply_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorResidue.lean)
-/
@[path]
lemma quotient_coprime_residue_equiv_apply_mk
  [CommRing O] [CommRing B] [Algebra O B]
  {q : Ideal B} [q.IsMaximal]
  {c : Ideal B}
  {o : O}
-- given
  (hc : ¬ c ≤ q)
  (hclear : ∀ x ∈ c, ∀ b : B, ∃ o : O, algebraMap O B o = x * b) :
-- imply
  quotient_coprime_residue_equiv q c hc hclear (Ideal.Quotient.mk _ o) =
      Ideal.Quotient.mk _ (algebraMap O B o) :=
-- proof
  rfl

end Ideal

namespace Ideal

/--
[nat_card_quotient_coprime_residue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorResidue.lean)
-/
@[path]
lemma nat_card_quotient_coprime_residue_eq
  [CommRing O] [CommRing B] [Algebra O B]
  {q : Ideal B} [q.IsMaximal]
  {c : Ideal B}
-- given
  (hc : ¬ c ≤ q)
  (hclear : ∀ x ∈ c, ∀ b : B, ∃ o : O, algebraMap O B o = x * b) :
-- imply
  Nat.card (O ⧸ q.comap (algebraMap O B)) = Nat.card (B ⧸ q) :=
-- proof
  Nat.card_congr (quotient_coprime_residue_equiv q c hc hclear).toEquiv

end Ideal

namespace Ideal

/--
[cardQuot_coprime_residue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorResidue.lean)
-/
@[path]
lemma cardQuot_coprime_residue_eq
  [CommRing O] [CommRing B] [Algebra O B]
  {q : Ideal B} [q.IsMaximal]
  {c : Ideal B}
-- given
  (hc : ¬ c ≤ q)
  (hclear : ∀ x ∈ c, ∀ b : B, ∃ o : O, algebraMap O B o = x * b) :
-- imply
  Submodule.cardQuot (q.comap (algebraMap O B) : Submodule O O) =
      Submodule.cardQuot (q : Submodule B B) := by
-- proof
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (quotient_coprime_residue_equiv q c hc hclear).toEquiv

end Ideal


-- created on 2026-10-20
-- updated on 2026-10-23
