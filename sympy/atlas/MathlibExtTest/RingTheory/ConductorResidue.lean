/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/ConductorResidue.lean -/


import Mathlib.Data.ZMod.Basic
import sympy.atlas.RingTheory.ConductorResidue
import Lemma.Ideal.ConductorResidue


noncomputable section

namespace MathlibExtTest.RingTheory.ConductorResidue

variable {O B : Type*} [CommRing O] [CommRing B] [Algebra O B]
variable (q : Ideal B) [q.IsMaximal] (c : Ideal B)
variable (hc : ¬ c ≤ q)
variable (hclear : ∀ x ∈ c, ∀ b : B, ∃ o : O, algebraMap O B o = x * b)

/-- The generic equivalence has the stated type. -/
example : O ⧸ q.comap (algebraMap O B) ≃+* B ⧸ q :=
  Ideal.quotient_coprime_residue_equiv q c hc hclear

/-- The generic `Nat.card` corollary. -/
example : Nat.card (O ⧸ q.comap (algebraMap O B)) = Nat.card (B ⧸ q) :=
  Ideal.nat_card_quotient_coprime_residue_eq q c hc hclear

/-- The generic `Submodule.cardQuot` corollary. -/
example : Submodule.cardQuot (q.comap (algebraMap O B) : Submodule O O) =
    Submodule.cardQuot (q : Submodule B B) :=
  Ideal.cardQuot_coprime_residue_eq q c hc hclear

/-- The simp lemma computes the equivalence on residue classes. -/
example (o : O) :
    Ideal.quotient_coprime_residue_equiv q c hc hclear (Ideal.Quotient.mk _ o) =
      Ideal.Quotient.mk _ (algebraMap O B o) := by
  simp

section Identity

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal]

/-- Identity-algebra specialization of the residue equivalence. -/
example : Nonempty (R ⧸ p.comap (algebraMap R R) ≃+* R ⧸ p) :=
  ⟨Ideal.quotient_coprime_residue_equiv p ⊤ (top_not_le_of_isMaximal p)
    (top_clears_identity)⟩

/-- Identity-algebra specialization of the `Nat.card` corollary. -/
example : Nat.card (R ⧸ p.comap (algebraMap R R)) = Nat.card (R ⧸ p) :=
  Ideal.nat_card_quotient_coprime_residue_eq p ⊤ (top_not_le_of_isMaximal p)
    (top_clears_identity)

end Identity

section Concrete

/-- Fully concrete instance: `ZMod 2` with `q = ⊥` and `c = ⊤` satisfies the
hypotheses, so the equivalence and both corollaries are non-vacuous. -/
example : Nonempty ((ZMod 2) ⧸ (⊥ : Ideal (ZMod 2)).comap (algebraMap (ZMod 2) _) ≃+*
    (ZMod 2) ⧸ (⊥ : Ideal (ZMod 2))) := by
  have _inst := Ideal.bot_isMaximal (K := ZMod 2)
  exact ⟨Ideal.quotient_coprime_residue_equiv ⊥ ⊤ (top_not_le_of_isMaximal ⊥)
    (top_clears_identity)⟩

example : Nat.card ((ZMod 2) ⧸ (⊥ : Ideal (ZMod 2)).comap (algebraMap (ZMod 2) _)) =
    Nat.card ((ZMod 2) ⧸ (⊥ : Ideal (ZMod 2))) := by
  have _inst := Ideal.bot_isMaximal (K := ZMod 2)
  exact Ideal.nat_card_quotient_coprime_residue_eq ⊥ ⊤ (top_not_le_of_isMaximal ⊥)
    (top_clears_identity)

end Concrete

end MathlibExtTest.RingTheory.ConductorResidue
