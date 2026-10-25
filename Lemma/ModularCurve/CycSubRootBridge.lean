import Mathlib
import Def.ModularCurve_TatePoint
import Lemma.WeierstrassCurve.OddOrderSummingSet
import Theorems.Thm_HahnSeries_isAlgClosed_rat
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_transcendental
import Theorems.Thm_WeierstrassCurve_natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open ModularCurve WeierstrassCurve Polynomial
open scoped Classical

namespace ModularCurve.TatePoint

theorem isAlgClosed_H : IsAlgClosed H := HahnSeries.isAlgClosed_rat

theorem charZero_H : CharZero H :=
  (RingHom.charZero_iff (HahnSeries.C (R := Qbar) (Γ := ℚ)).injective).mp inferInstance

attribute [local instance] isAlgClosed_H charZero_H

theorem transcendental_rat_of_transcendental_qbar {_ : Algebra ℚ H} {x : H}
    (hx : Transcendental Qbar x) : Transcendental ℚ x := by
  haveI := IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := Qbar) (A := H) (Subsingleton.elim _ _)
  exact hx.of_tower_top ℚ

theorem two_mul_pred_div_two_add_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    2 * ((p - 1) / 2) + 1 = p := by
  rcases (Fact.out : p.Prime).eq_two_or_odd' with h | h
  · exact absurd h hp2
  · obtain ⟨m, rfl⟩ := h; omega

section Gen

variable (E : WeierstrassCurve H) {p : ℕ}

def cycSubGen (G : CycSubH E p) : E.toAffine.Point := Classical.choose G.2

theorem addOrderOf_cycSubGen (G : CycSubH E p) : addOrderOf (cycSubGen E G) = p :=
  (Classical.choose_spec G.2).1

theorem coe_eq_zmultiples_cycSubGen (G : CycSubH E p) :
    G.1 = AddSubgroup.zmultiples (cycSubGen E G) :=
  (Classical.choose_spec G.2).2

theorem CycSubH.ext {G G' : CycSubH E p} (h : G.1 = G'.1) : G = G' := Subtype.ext h

def cycSubSummingSet (G : CycSubH E p) : Finset (H × H) :=
  E.oddOrderSummingSet (cycSubGen E G) ((p - 1) / 2)

theorem cycSubSummingSet_def (G : CycSubH E p) :
    cycSubSummingSet E G = E.oddOrderSummingSet (cycSubGen E G) ((p - 1) / 2) := rfl

end Gen

section Root

variable (E : WeierstrassCurve H) [E.IsElliptic] {p : ℕ} [Fact p.Prime]

theorem isElliptic_veluQuotient_cycSubSummingSet (hp2 : p ≠ 2) (G : CycSubH E p) :
    (E.veluQuotient (cycSubSummingSet E G)).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr
    (WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero (L := H) two_ne_zero E
      ((p - 1) / 2) (cycSubGen E G)
      (by rw [addOrderOf_cycSubGen, two_mul_pred_div_two_add_one hp2]))⟩

theorem isRoot_map_j_veluQuotient_j_of_eq {N : ℕ} [NeZero N] (n : ℕ) (hN : 2 * n + 1 = N)
    (data : ModularPolynomialData N) (Q : E.toAffine.Point) (hQ : addOrderOf Q = N)
    (hΔ : (E.veluQuotient (E.oddOrderSummingSet Q n)).Δ ≠ 0) :
    haveI : (E.veluQuotient (E.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom H) E.j)).IsRoot
      (E.veluQuotient (E.oddOrderSummingSet Q n)).j := by
  subst hN
  exact ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq E n Q hQ hΔ data

def cycSubRoot (hp2 : p ≠ 2) (data : ModularPolynomialData p) (G : CycSubH E p) : RootsAt data E.j :=
  ⟨@WeierstrassCurve.j H _ (E.veluQuotient (cycSubSummingSet E G))
      (isElliptic_veluQuotient_cycSubSummingSet E hp2 G),
    isRoot_map_j_veluQuotient_j_of_eq E ((p - 1) / 2) (two_mul_pred_div_two_add_one hp2) data
      (cycSubGen E G) (addOrderOf_cycSubGen E G)
      (isElliptic_veluQuotient_cycSubSummingSet E hp2 G).isUnit.ne_zero⟩

theorem cycSubRoot_coe (hp2 : p ≠ 2) (data : ModularPolynomialData p) (G : CycSubH E p) :
    (cycSubRoot E hp2 data G).1 =
      @WeierstrassCurve.j H _ (E.veluQuotient (cycSubSummingSet E G))
        (isElliptic_veluQuotient_cycSubSummingSet E hp2 G) := rfl

theorem cycSubRoot_injective (hp2 : p ≠ 2) (data : ModularPolynomialData p)
    (hj : Transcendental Qbar E.j) : Function.Injective (cycSubRoot E hp2 data) := by
  intro G G' h
  have hjj := congrArg Subtype.val h
  simp only [cycSubRoot_coe] at hjj
  apply CycSubH.ext
  rw [coe_eq_zmultiples_cycSubGen, coe_eq_zmultiples_cycSubGen]
  exact WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental E
    (transcendental_rat_of_transcendental_qbar hj) ((p - 1) / 2) (cycSubGen E G) (cycSubGen E G')
    (by rw [addOrderOf_cycSubGen, two_mul_pred_div_two_add_one hp2])
    (by rw [addOrderOf_cycSubGen, two_mul_pred_div_two_add_one hp2])
    (isElliptic_veluQuotient_cycSubSummingSet E hp2 G).isUnit.ne_zero
    (isElliptic_veluQuotient_cycSubSummingSet E hp2 G').isUnit.ne_zero hjj

end Root

section Count

variable (E : WeierstrassCurve H) {p : ℕ}

theorem exists_addOrderOf_eq_and_eq_zmultiples_iff {A : Type*} [AddCommGroup A] {N : ℕ}
    (G : AddSubgroup A) :
    (∃ g : A, addOrderOf g = N ∧ G = AddSubgroup.zmultiples g) ↔ (IsAddCyclic G ∧ Nat.card G = N) := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨inferInstance, by rw [Nat.card_zmultiples, hg]⟩
  · rintro ⟨hc, hcard⟩
    obtain ⟨g, hg⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top G).mp hc
    exact ⟨g, by rw [← Nat.card_zmultiples, hg, hcard], hg.symm⟩

theorem natCard_cycSubH [E.IsElliptic] [NeZero p] : Nat.card (CycSubH E p) = dedekindPsi p := by
  have h := WeierstrassCurve.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
    (K := H) E (n := p) (by exact_mod_cast NeZero.ne p)
  have hW : WeierstrassCurve.Affine.baseChange E H = E.toAffine := by
    rw [WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange, Algebra.algebraMap_self,
      WeierstrassCurve.map_id]
  rw [hW] at h
  rw [← h]
  unfold CycSubH
  exact Nat.card_congr (Equiv.subtypeEquivRight fun G =>
    exists_addOrderOf_eq_and_eq_zmultiples_iff G)

theorem le_dedekindPsi (N : ℕ) (hN : N ≠ 0) : N ≤ dedekindPsi N := by
  unfold dedekindPsi
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hN, squarefree_one⟩
  simpa using Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1

theorem finite_cycSubH [E.IsElliptic] [NeZero p] : Finite (CycSubH E p) :=
  Nat.finite_of_card_ne_zero (by
    rw [natCard_cycSubH]
    exact (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne p)) (le_dedekindPsi p (NeZero.ne p))).ne')

def rootsAtEquivMemRootsToFinset [NeZero p] (data : ModularPolynomialData p) (jv : H) :
    RootsAt data jv ≃
      {y : H // y ∈ (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom H) jv)).roots.toFinset} := by
  unfold RootsAt
  exact Equiv.subtypeEquivRight fun y => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots ((data.monic.map _).ne_zero)]

theorem finite_rootsAt [NeZero p] (data : ModularPolynomialData p) (jv : H) :
    Finite (RootsAt data jv) :=
  Finite.of_equiv _ (rootsAtEquivMemRootsToFinset data jv).symm

theorem natCard_rootsAt_le [NeZero p] (data : ModularPolynomialData p) (jv : H) :
    Nat.card (RootsAt data jv) ≤ dedekindPsi p := by
  rw [Nat.card_congr (rootsAtEquivMemRootsToFinset data jv), Nat.card_eq_finsetCard]
  set f := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom H) jv) with hf
  calc f.roots.toFinset.card ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ = dedekindPsi p := by rw [hf, data.monic.natDegree_map, data.natDegree_eq]

end Count

section Equiv

variable (E : WeierstrassCurve H) [E.IsElliptic] {p : ℕ} [Fact p.Prime]

theorem cycSubRoot_bijective (hp2 : p ≠ 2) (data : ModularPolynomialData p)
    (hj : Transcendental Qbar E.j) : Function.Bijective (cycSubRoot E hp2 data) := by
  haveI := finite_rootsAt data E.j
  refine (cycSubRoot_injective E hp2 data hj).bijective_of_nat_card_le ?_
  rw [natCard_cycSubH]
  exact natCard_rootsAt_le data E.j

def rootsEquivCycSubH (hp2 : p ≠ 2) (data : ModularPolynomialData p)
    (hj : Transcendental Qbar E.j) : RootsAt data E.j ≃ CycSubH E p :=
  (Equiv.ofBijective (cycSubRoot E hp2 data) (cycSubRoot_bijective E hp2 data hj)).symm

theorem rootsEquivCycSubH_symm_apply (hp2 : p ≠ 2) (data : ModularPolynomialData p)
    (hj : Transcendental Qbar E.j) (G : CycSubH E p) :
    (rootsEquivCycSubH E hp2 data hj).symm G = cycSubRoot E hp2 data G := rfl

theorem rootsEquivCycSubH_apply_eq_iff (hp2 : p ≠ 2) (data : ModularPolynomialData p)
    (hj : Transcendental Qbar E.j) (r : RootsAt data E.j) (G : CycSubH E p) :
    rootsEquivCycSubH E hp2 data hj r = G ↔ r = cycSubRoot E hp2 data G := by
  rw [← rootsEquivCycSubH_symm_apply E hp2 data hj G, Equiv.eq_symm_apply]

end Equiv

end ModularCurve.TatePoint

end
