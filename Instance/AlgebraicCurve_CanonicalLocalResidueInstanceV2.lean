-- Carved from Lemma/Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean: instance decls only.
import Mathlib
import Class.AlgebraicCurve_LocalResidue
import Instance.AlgebraicCurve_IsCurveOver
import Class.AlgebraicCurve_DivisorPushPull
import Instance.AlgebraicCurve_PlaceCompletion
import Def.AlgebraicCurve_WeilOfKaehler
import Structure.AlgebraicCurve_CanonicalLocalResidueInstanceV2

set_option autoImplicit false
set_option maxHeartbeats 1600000

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

instance HasSeparableResidue.of_perfectField [PerfectField K]
    [∀ v : Place K F, v.FiniteResidue] : HasSeparableResidue K F where
  trace_ne_zero v :=
    haveI : Module.Finite K v.ResidueField := Place.FiniteResidue.finite
    Algebra.trace_ne_zero K v.ResidueField

instance HasSeparableResidue.of_perfectField_of_isCurveOver [PerfectField K]
    [IsCurveOver K F] : HasSeparableResidue K F :=
  HasSeparableResidue.of_perfectField


end AlgebraicCurve

end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000


set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

namespace AlgebraicCurve


namespace Place

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']

instance instIsLocalHom_restrictSubringHom : IsLocalHom (w.restrictSubringHom (F := F)) := by
  constructor
  intro a ha

  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
  have hb' : algebraMap F F' (a : F) * (b : F') = 1 := by
    exact congrArg Subtype.val hb
  have ha0 : (a : F) ≠ 0 := by
    rintro h0
    rw [h0, map_zero, zero_mul] at hb'
    exact zero_ne_one hb'

  have hbeq : (b : F') = algebraMap F F' (a : F)⁻¹ := by
    rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_right (by linear_combination hb')

  have hmem : (a : F)⁻¹ ∈ (w.restrict F).toValuationSubring := by
    show algebraMap F F' (a : F)⁻¹ ∈ w.toValuationSubring
    exact hbeq ▸ b.2
  exact isUnit_iff_exists_inv.mpr
    ⟨⟨(a : F)⁻¹, hmem⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

instance instAlgebra_restrictResidueField : Algebra (w.restrict F).ResidueField w.ResidueField :=
  (w.residueFieldMapRestrict (F := F)).toAlgebra

instance instIsScalarTower_restrictResidueField : IsScalarTower K (w.restrict F).ResidueField w.ResidueField := by
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show IsLocalRing.residue _ (algebraMap K w.toValuationSubring a)
      = algebraMap (w.restrict F).ResidueField w.ResidueField
          (IsLocalRing.residue _ (algebraMap K (w.restrict F).toValuationSubring a))
  rw [algebraMap_residueField_residue]
  congr 1
  ext
  show algebraMap K F' a = algebraMap F F' (algebraMap K F a)
  rw [IsScalarTower.algebraMap_apply K F F']

end Restrict

end Place
end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]


instance instHasLocalResidue : HasLocalResidue K F where
  exists_data v := ⟨v.localResidueDataOfExtend⟩

variable [HasCanonicalLocalResidueKStar K F]

end AlgebraicCurve

end

set_option autoImplicit false


set_option autoImplicit false


set_option autoImplicit false


set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]


instance instHasCanonicalLocalResidueK : HasCanonicalLocalResidueK K F where
  exists_data v := ⟨v.canonicalLocalResidueDataKOfExtend⟩


end AlgebraicCurve

end

set_option autoImplicit false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000


set_option autoImplicit false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000


set_option autoImplicit false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000


set_option autoImplicit false
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve.Lg37 Polynomial IntermediateField Mp72a102T1 Mp72a102T2


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000


set_option autoImplicit false
set_option maxHeartbeats 1600000

open Polynomial IsLocalRing AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.Mp72a102T3 Mp72a103T2 Mp72a102T1
open ModularCurve.KwNo6Section

namespace ModularCurve.KwNo6Pin

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

instance isLocalRing_completion (v : Place K F) :
    IsLocalRing (lg37_completion v) := by
  haveI := map_isMaximal v
  haveI := isAdicComplete_map v
  exact isLocalRing_of_isAdicComplete_maximal
    ((maximalIdeal v.toValuationSubring).map
      (algebraMap v.toValuationSubring (lg37_completion v)))

end ModularCurve.KwNo6Pin

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Polynomial IsLocalRing AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.Mp72a102T3 Mp72a103T2 Mp72a102T1
open ModularCurve.KwNo6Section


set_option autoImplicit false
set_option maxHeartbeats 1600000

open Polynomial IsLocalRing AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.KwNo6Section ModularCurve.KwNo6Pin
open Mp72a102T1

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable instance instHasCanonicalLocalResidueKStar [IsCurveOver K F] [PerfectField K] :
    HasCanonicalLocalResidueKStar K F where
  dataKStar v :=
    haveI : FiniteDimensional K v.ResidueField := Place.FiniteResidue.finite
    haveI : Algebra.IsSeparable K v.ResidueField :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    canonicalLocalResidueDataKStar v
      (Classical.choice (completionSection_nonempty_generic v))

end AlgebraicCurve
