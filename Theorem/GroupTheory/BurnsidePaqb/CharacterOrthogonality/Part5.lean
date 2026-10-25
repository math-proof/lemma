/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean -/

import Theorem.GroupTheory.BurnsidePaqbReduction.Part2
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Complex.Basic
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Def.GroupTheory.BurnsidePaqb.CharacterOrthogonality.Part4
open CategoryTheory

/-!
Character-orthogonality stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/ColumnOrth.lean`.
-/


namespace BurnsidePaqb

variable (G : Type) [Group G] [Fintype G]

/-- Every finite set of iso-classes has cardinality at most `|G|`. -/
theorem cardBound (s : Finset (Irr G)) : s.card ≤ Fintype.card G := by
  classical
  have hli : LinearIndependent ℂ (fun i : ↥s => Irr.charFun G (i : Irr G)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hfun : ∀ x : G, (∑ i, g i • Irr.charFun G ((i : ↥s) : Irr G) x) = 0 := by
      intro x
      have hcon := congrFun hg x
      simpa using hcon
    intro j
    have hexpand : (Nat.card G : ℂ)⁻¹ *
        ∑ x : G, (∑ i, g i • Irr.charFun G ((i : ↥s) : Irr G) x) *
          Irr.charFun G ((j : ↥s) : Irr G) x⁻¹ = g j := by
      have step1 : ∑ x : G, (∑ i, g i • Irr.charFun G ((i : ↥s) : Irr G) x) *
          Irr.charFun G ((j : ↥s) : Irr G) x⁻¹
          = ∑ i, g i * (∑ x : G, Irr.charFun G ((i : ↥s) : Irr G) x *
            Irr.charFun G ((j : ↥s) : Irr G) x⁻¹) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        simp [smul_eq_mul, mul_assoc]
      rw [step1, Finset.mul_sum]
      trans ∑ i : ↥s, (if ((i : ↥s) : Irr G) = (j : ↥s) then g i else 0)
      · refine Finset.sum_congr rfl fun i _ => ?_
        have hi := charInner_orth G ((i : ↥s) : Irr G) ((j : ↥s) : Irr G)
        rw [mul_left_comm, hi]
        by_cases hij : ((i : ↥s) : Irr G) = (j : ↥s)
        · rw [ite_eq_left hij, ite_eq_left hij, mul_one]
        · rw [ite_eq_right hij, ite_eq_right hij, mul_zero]
      · simp_rw [Subtype.ext_iff.symm]
        exact Fintype.sum_ite_eq' j g
    have h2 : (Nat.card G : ℂ)⁻¹ *
        ∑ x : G, (∑ i, g i • Irr.charFun G ((i : ↥s) : Irr G) x) *
          Irr.charFun G ((j : ↥s) : Irr G) x⁻¹ = 0 := by
      simp_rw [hfun, zero_mul, Finset.sum_const_zero, mul_zero]
    rw [hexpand] at h2
    exact h2
  have h := LinearIndependent.fintype_card_le_finrank hli
  rw [Module.finrank_pi] at h
  rwa [Fintype.card_coe] at h

end BurnsidePaqb
