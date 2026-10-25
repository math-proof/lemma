/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/Artin.lean -/


import Def.NumberTheory.LSeries.Artin
import Lemma.Nat.LSeries.Artin
import Def.MathlibExtTest.NumberTheory.LSeries.Artin


namespace RepresentationTest

open Representation

-- Elaboration checks for the local factor and formal product.
noncomputable example : ℂ :=
  artinLocalFactorRaw (Representation.trivial ℂ Unit ℂ)
    primeTwo unitLocalDatum 0

noncomputable example : ℂ :=
  artinEulerProductOfLocalData (Representation.trivial ℂ Unit ℂ)
    (fun _ => unitLocalDatum) 2

-- `artinLocalFactorRaw_zero` exposes totalization at `s = 0`.
example : artinLocalFactorRaw (Representation.trivial ℂ Unit ℂ)
    primeTwo unitLocalDatum 0 =
      (LinearMap.det (LinearMap.id -
        ((Representation.quotientToInvariants
          ((Representation.trivial ℂ Unit ℂ).comp unitLocalDatum.decomposition.subtype :
            Representation ℂ unitLocalDatum.decomposition ℂ)
          unitLocalDatum.inertia) unitLocalDatum.frobenius)))⁻¹ := by
  exact artinLocalFactorRaw_zero _ _ _

-- The regularity predicate exposes the non-pole domain of the raw inverse.
example (s : ℂ)
    (h : ArtinLocalFactorRegular (Representation.trivial ℂ Unit ℂ)
      primeTwo unitLocalDatum s) :
    artinLocalFactorRaw (Representation.trivial ℂ Unit ℂ)
      primeTwo unitLocalDatum s ≠ 0 :=
  artinLocalFactorRaw_ne_zero _ _ _ _ h

-- A `HasArtinEulerProduct` witness extracts the value of the raw `tprod`.
example (z : ℂ)
    (h : HasArtinEulerProduct (Representation.trivial ℂ Unit ℂ)
      (fun _ => unitLocalDatum) 2 z) :
    artinEulerProductOfLocalData (Representation.trivial ℂ Unit ℂ)
      (fun _ => unitLocalDatum) 2 = z :=
  artinEulerProductOfLocalData_eq_of_hasProd _ _ _ _ h

-- A nonzero product witness also rules out every totalized pole factor.
example (s z : ℂ)
    (h : HasNonzeroArtinEulerProduct (Representation.trivial ℂ Unit ℂ)
      (fun _ => unitLocalDatum) s z) :
    ArtinLocalFactorRegular (Representation.trivial ℂ Unit ℂ)
      primeTwo unitLocalDatum s :=
  h.localFactorRegular primeTwo

-- The identity-action formula records the invariant-space dimension in general.
example (s : ℂ) :
    artinLocalFactorRaw (Representation.trivial ℂ Unit ℂ)
      primeTwo unitLocalDatum s =
        ((1 - (2 : ℂ) ^ (-s)) ^ Module.finrank ℂ (invariants
          (((Representation.trivial ℂ Unit ℂ).comp
            unitLocalDatum.decomposition.subtype :
              Representation ℂ unitLocalDatum.decomposition ℂ).comp
                unitLocalDatum.inertia.subtype)))⁻¹ := by
  apply artinLocalFactorRaw_of_action_eq_id_general
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

-- Degree-one trivial quotient action yields the Riemann local factor.
example (s : ℂ) :
    artinLocalFactorRaw (Representation.trivial ℂ Unit ℂ)
      primeTwo unitLocalDatum s = (1 - (2 : ℂ) ^ (-s))⁻¹ := by
  apply artinLocalFactorRaw_of_action_eq_id
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  · let ρI :=
      (((Representation.trivial ℂ Unit ℂ).comp unitLocalDatum.decomposition.subtype :
        Representation ℂ unitLocalDatum.decomposition ℂ).comp
          unitLocalDatum.inertia.subtype)
    let htriv : Representation.IsTrivial ρI := ⟨fun _ => rfl⟩
    change Module.finrank ℂ (invariants ρI) = 1
    rw [@Representation.invariants_eq_top _ _ _ _ _ _ _ ρI htriv]
    simp

end RepresentationTest
