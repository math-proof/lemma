-- Carved from Lemma/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean: instance decls only.
import Instance.AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Class.AlgebraicCurve_DivisorPushPull

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing


set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']

namespace Place

variable (w : Place K F')

instance instIsLocalHomRestrictInclusion : IsLocalHom (restrictInclusion F w) where
  map_nonunit a ha := by

    have hord : w.ord (algebraMap F F' (a : F)) = 0 := by
      have h := w.ord_coe_unit ha.unit
      rwa [IsUnit.unit_spec, coe_restrictInclusion] at h

    have ha0 : (a : F) ≠ 0 := by
      rintro h0
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
      have hb' : algebraMap F F' (a : F) * (b : F') = 1 := congrArg Subtype.val hb
      rw [h0, map_zero, zero_mul] at hb'
      exact zero_ne_one hb'
    exact (isUnit_mk_comap_iff ha0 a.2).mpr hord

instance instAlgebraResidueFieldRestrictPushforward :
    Algebra (w.restrict F).ResidueField w.ResidueField :=
  (restrictResidueMap F w).toAlgebra

instance instIsScalarTowerResidueFieldRestrictPushforward :
    IsScalarTower K (w.restrict F).ResidueField w.ResidueField := by
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show IsLocalRing.residue _ (algebraMap K w.toValuationSubring a) =
    restrictResidueMap F w
      (IsLocalRing.residue _ (algebraMap K (w.restrict F).toValuationSubring a))
  rw [restrictResidueMap_residue]
  refine congrArg _ (Subtype.ext ?_)
  show algebraMap K F' a = algebraMap F F' (algebraMap K F a)
  rw [← IsScalarTower.algebraMap_apply]

end Place


end AlgebraicCurve

set_option autoImplicit false

noncomputable section


set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']

instance (priority := 100) instFundamentalIdentityOfSumRamificationInertia
    [SumRamificationInertia K F F'] : FundamentalIdentity K F F' where
  sum_ramificationIndex_mul_deg v := by
    have key := SumRamificationInertia.sum_ramificationIndex_mul_inertiaDeg
      (K := K) (F := F) (F' := F') v
    calc
      ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
          = ∑ w ∈ v.fiber F',
              (v.deg : ℤ) * ((w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)) := by
            refine Finset.sum_congr rfl fun w hw => ?_
            have htower : ((w.restrict F).deg : ℤ) * (w.inertiaDeg F : ℤ) = (w.deg : ℤ) := by
              exact_mod_cast congrArg (Nat.cast (R := ℤ))
                (w.deg_restrict_mul_inertiaDeg (F := F))
            rw [Place.mem_fiber.mp hw] at htower
            rw [← htower]; ring
      _ = (v.deg : ℤ) * ∑ w ∈ v.fiber F',
              (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) := by
            rw [Finset.mul_sum]
      _ = (Module.finrank F F' : ℤ) * (v.deg : ℤ) := by rw [key]; ring


end AlgebraicCurve
end
end
end
end
