module
public import Mathlib
public import Def.GaloisRep_Flat
public import Theorem.Thm_GaloisRep_isLocalization_ratLocalizedAt


public section

namespace GaloisRep

noncomputable section


def ratLocalizedAtResidue (q : ℕ) [Fact q.Prime] : ↥(ratLocalizedAt q) →+* ZMod q :=
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := q) Fact.out
  IsLocalization.lift (M := (Ideal.span {(q : ℤ)}).primeCompl) (S := ↥(ratLocalizedAt q))
    (g := Int.castRingHom (ZMod q))
    (fun y => by
      refine isUnit_iff_ne_zero.mpr ?_
      simp only [Int.coe_castRingHom, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro h
      exact y.2 (Ideal.mem_span_singleton.mpr (by exact_mod_cast h)))

end

end GaloisRep
