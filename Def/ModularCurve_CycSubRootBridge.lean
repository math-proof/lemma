module
public import Mathlib
public import Def.ModularCurve_TatePoint
public import Theorem.WeierstrassCurve.OddOrderSummingSet
public import Theorem.RingTheory.HahnSeries.IsAlgClosed
public import Theorem.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero
public import Theorem.Thm_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq
public import Theorem.Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_transcendental
public import Theorem.Thm_WeierstrassCurve_natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000


public section

noncomputable section

open ModularCurve WeierstrassCurve Polynomial
open scoped Classical

namespace ModularCurve.TatePoint

section Gen

variable (E : WeierstrassCurve H) {p : ℕ}

def cycSubGen (G : CycSubH E p) : E.toAffine.Point := Classical.choose G.2

def cycSubSummingSet (G : CycSubH E p) : Finset (H × H) :=
  E.oddOrderSummingSet (cycSubGen E G) ((p - 1) / 2)

end Gen

section Root

variable (E : WeierstrassCurve H) [E.IsElliptic] {p : ℕ} [Fact p.Prime]

def cycSubRoot (hp2 : p ≠ 2) (data : ModularPolynomialData p) (G : CycSubH E p) : RootsAt data E.j :=
  ⟨@WeierstrassCurve.j H _ (E.veluQuotient (cycSubSummingSet E G))
      (isElliptic_veluQuotient_cycSubSummingSet E hp2 G),
    isRoot_map_j_veluQuotient_j_of_eq E ((p - 1) / 2) (two_mul_pred_div_two_add_one hp2) data
      (cycSubGen E G) (addOrderOf_cycSubGen E G)
      (isElliptic_veluQuotient_cycSubSummingSet E hp2 G).isUnit.ne_zero⟩

end Root

section Count

variable (E : WeierstrassCurve H) {p : ℕ}

def rootsAtEquivMemRootsToFinset [NeZero p] (data : ModularPolynomialData p) (jv : H) :
    RootsAt data jv ≃
      {y : H // y ∈ (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom H) jv)).roots.toFinset} := by
  unfold RootsAt
  exact Equiv.subtypeEquivRight fun y => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots ((data.monic.map _).ne_zero)]

end Count

section Equiv

variable (E : WeierstrassCurve H) [E.IsElliptic] {p : ℕ} [Fact p.Prime]

def rootsEquivCycSubH (hp2 : p ≠ 2) (data : ModularPolynomialData p)
    (hj : Transcendental Qbar E.j) : RootsAt data E.j ≃ CycSubH E p :=
  (Equiv.ofBijective (cycSubRoot E hp2 data) (cycSubRoot_bijective E hp2 data hj)).symm

end Equiv

end ModularCurve.TatePoint

end
