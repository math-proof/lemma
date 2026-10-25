/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SimplePrime.lean -/

import Lemma.Nat.Any_Eq_MulPowS.of.Prime.Prime
import Def.GroupTheory.BurnsidePaqb.KillingLemma
import Lemma.Representation.Character.eq.SumRootsCharpoly
import Lemma.Representation.All_All_Eq.of.EqNormCharacter_FinrankV
import Lemma.Representation.IsIrreducible.of.EqRepresentationG
import Instance.GroupTheory.BurnsidePaqb.ScalarCenter
import Def.GroupTheory.BurnsidePaqb.CharacterOrthogonality.Part6
import Theorem.GroupTheory.BurnsidePaqb.SimplePrime
/-!
Simple-prime-power stage of the complete Burnside proof.

Authors: Muse Spark 1.3, @toskua, Avocado
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/SimplePrime.lean`.
-/


namespace BurnsidePaqb

variable {G : Type*} [Group G] [Fintype G]

open Classical in
/-- The scalar character of a degree-1 representation, as a hom to units. -/
noncomputable def linearCharHom {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (ρ : Representation ℂ G V)
    (hd : Module.finrank ℂ V = 1) : G →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ρ.character g
      map_one' := by rw [Representation.char_one, hd]; simp
      map_mul' := fun g h => by
        have h1 := eq_smul_one_of_finrank_one ρ hd g
        have h2 := eq_smul_one_of_finrank_one ρ hd h
        have h3 := eq_smul_one_of_finrank_one ρ hd (g * h)
        have hmul : ρ (g * h) = ρ g * ρ h := map_mul ρ g h
        have htr : ρ.character (g * h)
            = ρ.character g * ρ.character h := by
          have e : (ρ.character (g * h)) • (1 : Module.End ℂ V)
              = (ρ.character g * ρ.character h) • 1 := by
            rw [← h3, hmul, h1, h2, smul_mul_smul, one_mul]
          exact smul_left_injective ℂ (one_ne_zero : (1 : Module.End ℂ V) ≠ 0) e
        exact htr }

end BurnsidePaqb
