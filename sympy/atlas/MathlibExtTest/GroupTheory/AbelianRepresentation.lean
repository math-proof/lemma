/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/AbelianRepresentation.lean -/


import sympy.atlas.GroupTheory.AbelianRepresentation
import Lemma.Representation.IsIrreducible
import Mathlib.Analysis.Complex.Polynomial.Basic

open CategoryTheory
open scoped IsMulCommutative

open MathlibExt.GroupTheory.AbelianRepresentationWanted

namespace MathlibExtTest.GroupTheory.AbelianRepresentation

-- A simple character takes values whose `Nat.card G`-th powers are one.
example (G : Type*) [CommGroup G] [Finite G] (V : FDRep ℂ G) [Simple V]
    (g : G) : V.character g ^ Nat.card G = 1 := by
  obtain ⟨φ, hφ⟩ := abelian_simple_char_is_hom G V
  rw [hφ]
  have hg : g ^ Nat.card G = 1 := pow_card_eq_one'
  simpa only [map_pow, map_one] using congrArg φ hg

-- A simple representation is recovered from its character as a one-dimensional representation.
example (G : Type*) [CommGroup G] [Finite G] (V : FDRep ℂ G) [Simple V] :
    Nonempty (V ≅ FDRep.ofMonoidHom V.characterMonoidHom) := by
  let _ : Simple (FDRep.ofMonoidHom V.characterMonoidHom) :=
    FDRep.ofMonoidHom_simple _
  apply abelian_simple_iso_of_char_eq G
  simp

end MathlibExtTest.GroupTheory.AbelianRepresentation
