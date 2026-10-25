/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SimplePrime.lean -/

import Lemma.Nat.Any_Eq_MulPowS.of.Prime.Prime
import Def.GroupTheory.BurnsidePaqb.KillingLemma
import Lemma.Representation.Character.eq.SumRootsCharpoly
import Lemma.Representation.All_All_Eq.of.EqNormCharacter_FinrankV
import Lemma.Representation.IsIrreducible.of.EqRepresentationG
import Instance.GroupTheory.BurnsidePaqb.ScalarCenter
import Def.GroupTheory.BurnsidePaqb.CharacterOrthogonality.Part6
/-!
Simple-prime-power stage of the complete Burnside proof.

Authors: Muse Spark 1.3, @toskua, Avocado
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/SimplePrime.lean`.
-/


namespace BurnsidePaqb

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
/-- In degree 1, every representation operator is a scalar. -/
theorem eq_smul_one_of_finrank_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hd : Module.finrank ℂ V = 1) (g : G) :
    ρ g = ρ.character g • 1 := by
  have b := Module.finBasis ℂ V
  rw [hd] at b
  set d : ℂ := b.repr (ρ g (b 0)) 0 with hddef
  have hexpand : ∀ x : V, x = b.repr x 0 • b 0 := fun x => by
    have h := Module.Basis.sum_repr b x
    rw [Fin.sum_univ_one] at h
    exact h.symm
  have hfb0 : ρ g (b 0) = d • b 0 := hexpand _
  have hfg : ρ g = d • 1 := by
    apply Module.Basis.ext b
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [hfb0]
    simp
  have hχ : ρ.character g = d := by
    have htr : LinearMap.trace ℂ V (ρ g) = d := by
      rw [hfg, map_smul]
      simp [hd, smul_eq_mul]
    exact htr
  rw [hχ]
  exact hfg

end BurnsidePaqb
