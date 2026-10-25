/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean -/

import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Theorem.GroupTheory.BurnsidePaqb.ClassSum.Part3
import Lemma.Nat.ConjClass.of.IsConj
import Def.GroupTheory.BurnsidePaqb.CentralCharacter
/-!
Central-character stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/CentralChar.lean`.
-/


namespace BurnsidePaqb

variable {G : Type*} [Group G] [Fintype G]

section CentralScalar

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

variable (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]

open Classical in
theorem centralScalar_spec (l : ConjClasses G) (v : V) :
    ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset) v
      = centralScalar ρ l • v :=
  Classical.choose_spec
    (exists_scalar_of_central ρ (classSum (ConjClasses.carrier l).toFinset)
      (classSum_carrier_central l)) v

open Classical in
/-- Central scalars multiply with the structure constants. -/
theorem centralScalar_mul (l1 l2 : ConjClasses G) :
    centralScalar ρ l1 * centralScalar ρ l2
      = ∑ l, (structConst (conjClass (classRep l1)) (conjClass (classRep l2))
          (classRep l) : ℂ) * centralScalar ρ l := by
  classical
  have hend : ρ.asAlgebraHom (classSum (ConjClasses.carrier l1).toFinset)
        * ρ.asAlgebraHom (classSum (ConjClasses.carrier l2).toFinset)
      = ∑ l, (structConst (conjClass (classRep l1)) (conjClass (classRep l2))
          (classRep l) : ℂ)
          • ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset) := by
    rw [carrier_toFinset, carrier_toFinset, ← map_mul, classSum_mul, map_sum]
    simp only [map_smul]
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hpoint : (ρ.asAlgebraHom (classSum (ConjClasses.carrier l1).toFinset)
        * ρ.asAlgebraHom (classSum (ConjClasses.carrier l2).toFinset)) v
      = (∑ l, (structConst (conjClass (classRep l1)) (conjClass (classRep l2))
          (classRep l) : ℂ)
          • ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset)) v :=
    congrArg (fun F : Module.End ℂ V => F v) hend
  rw [Module.End.mul_apply, LinearMap.sum_apply] at hpoint
  simp only [LinearMap.smul_apply, centralScalar_spec, smul_smul] at hpoint
  rw [← Finset.sum_smul] at hpoint
  have hsub : (centralScalar ρ l1 * centralScalar ρ l2
      - ∑ l, (structConst (conjClass (classRep l1)) (conjClass (classRep l2))
          (classRep l) : ℂ) * centralScalar ρ l) • v = 0 := by
    rw [sub_smul, hpoint, sub_self]
  rcases smul_eq_zero.mp hsub with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv

end CentralScalar
end BurnsidePaqb
