import Mathlib
import Lemma.WeierstrassCurve.ReduceHom
import Instance.WeierstrassCurve_ZeroComponentReduction

set_option autoImplicit false

open IsLocalRing Finset

namespace ValuationSubring

variable {L : Type*} [Field L] (A : ValuationSubring L)


end ValuationSubring

variable {L : Type*} [Field L]

structure FormalCoordinates (A : ValuationSubring L) (G : Type*) [AddCommGroup G]
    (d : ℕ) where

  disc : AddSubgroup G

  coord : G → Fin d → L

  coord_mem_nonunits : ∀ P ∈ disc, ∀ i, coord P i ∈ A.nonunits

  eq_zero_of_coord_eq_zero : ∀ P ∈ disc, (∀ i, coord P i = 0) → P = 0

  coord_zero : ∀ i, coord 0 i = 0

  coord_nsmul_sub : ∀ P ∈ disc, ∀ (n : ℕ) (i : Fin d), ∃ c : Fin d → L,
    (∀ j, c j ∈ A.nonunits) ∧
    coord (n • P) i - n * coord P i = ∑ j, c j * coord P j

namespace FormalCoordinates

variable {A : ValuationSubring L} {G : Type*} [AddCommGroup G] {d : ℕ}


end FormalCoordinates

set_option autoImplicit false

namespace ModularCurve

namespace ElevenA1

open WeierstrassCurve Affine

section Count

variable {K : Type*} [CommRing K] (W : WeierstrassCurve.Affine K)

end Count

end ElevenA1

end ModularCurve

set_option autoImplicit false

open IsLocalRing ValuationSubring WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace WeierstrassCurve

variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)


variable [DecidableEq L]


end WeierstrassCurve

set_option autoImplicit false

open IsLocalRing

namespace WeierstrassCurve

section General

variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

def HasNonsingularReduction (P : (W.map A.subtype).toAffine.Point) : Prop :=
  ∀ x y (h : (W.map A.subtype).toAffine.Nonsingular x y), P = .some x y h →
    ∀ (hx : x ∈ A) (hy : y ∈ A),
      (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩)


section NonIntegralLocus

variable [DecidableEq L]


end NonIntegralLocus


open Classical in

noncomputable def reducePointSmooth :
    (W.map A.subtype).toAffine.Point → (W.map (residue A)).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : x ∈ A then
      if hns : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩)
          (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩) then
        .some _ _ hns
      else .zero
    else .zero

@[simp]


section Kernel

variable [DecidableEq L]


end Kernel


section Slope

variable [DecidableEq L]


end Slope

section Carrier

variable [DecidableEq L] [DecidableEq (ResidueField A)]

structure SmoothLocusReductionData : Type _ where

  zeroComponent : AddSubgroup (W.map A.subtype).toAffine.Point

  mem_iff : ∀ P : (W.map A.subtype).toAffine.Point,
    P ∈ zeroComponent ↔ W.HasNonsingularReduction P

  reducePointSmooth_add : ∀ P Q : (W.map A.subtype).toAffine.Point,
    P ∈ zeroComponent → Q ∈ zeroComponent →
      W.reducePointSmooth (P + Q) = W.reducePointSmooth P + W.reducePointSmooth Q

namespace SmoothLocusReductionData

variable {W}


end SmoothLocusReductionData

end Carrier

end General

section ConsumerEngine

variable {L : Type} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve A}
  [DecidableEq L] [DecidableEq (ResidueField A)]

end ConsumerEngine

end WeierstrassCurve

set_option autoImplicit false

open IsLocalRing

namespace WeierstrassCurve

variable {L : Type*} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve A}


section CoordinatewiseEngine

variable [DecidableEq L] [DecidableEq (ResidueField A)]


set_option maxHeartbeats 800000 in


set_option maxHeartbeats 800000 in


end CoordinatewiseEngine

section CaseAnalysis

variable [DecidableEq L] [DecidableEq (ResidueField A)]

set_option maxHeartbeats 1600000 in


set_option maxHeartbeats 800000 in


end CaseAnalysis

section Closure

variable [DecidableEq L] [DecidableEq (ResidueField A)]


end Closure

section Carrier

variable [DecidableEq L] [DecidableEq (ResidueField A)]

variable (W) in


variable (W) in

variable (W) in


variable (W) in


variable (W) in


variable (W) in


variable (W) in


end Carrier

end WeierstrassCurve
