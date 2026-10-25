/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part21


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decFormalRootedLogCoeff_eq_boundedRootSum
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    ons_decFormalRootedLogCoeff L a b d m =
      -(∑ root : ons_DecRootedAtomBounded L d
          (ons_finsuppTotalDegree m),
        if ons_decBoundedRootExponent root = m then
          ons_decBoundedRootWeight L a b root /
            (ons_visitCount d root.2.1 : ℂ)
        else 0) := by
  classical
  unfold ons_decFormalRootedLogCoeff
  apply congrArg Neg.neg
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r hr
  rw [ons_decFormalFixedBucketE_div_eq_rerooted]
  change (∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (r.val + 1) → ons_Dart L ↦
        loop 0 = d ∧ ∀ j, loop j ≠ ons_dartRev L d),
      (if ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
       else 0) / (ons_visitCount d loop : ℂ)) =
    ∑ loop : {loop : Fin (r.val + 1) → ons_Dart L //
        loop 0 = d ∧ ∀ j, loop j ≠ ons_dartRev L d},
      if ons_decLoopExponent L loop.1 = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop.1 /
            (ons_visitCount d loop.1 : ℂ)
      else 0
  rw [← Finset.sum_subtype
    (s := Finset.univ.filter (fun loop : Fin (r.val + 1) → ons_Dart L ↦
      loop 0 = d ∧ ∀ j, loop j ≠ ons_dartRev L d))
    (by simp)
    (fun loop : Fin (r.val + 1) → ons_Dart L ↦
      if ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop /
            (ons_visitCount d loop : ℂ)
      else 0)]
  rw [Finset.sum_filter]
  rw [Finset.sum_ite]
  simp
  apply Finset.sum_congr rfl
  intro loop hloop
  by_cases hexponent : ons_decLoopExponent L loop = m
  · simp [hexponent]
  · simp [hexponent]

theorem ons_decFormalRootedLogCoeff_eq_zero_of_external_zero
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hzero : m s(d, ons_dartRev L d) = 0) :
    ons_decFormalRootedLogCoeff L a b d m = 0 := by
  rw [ons_decFormalRootedLogCoeff_eq_boundedRootSum]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro root hroot
  rw [if_neg]
  intro hexponent
  have hvisit := ons_decRootedAtom_externalExponent_eq_visitCount
    L d (ons_decForgetBoundedRoot root)
  rw [ons_decForgetBoundedRoot_exponent, hexponent, hzero] at hvisit
  change 0 = ons_visitCount d root.2.1 at hvisit
  have hpos : 0 < ons_visitCount d root.2.1 :=
    (ons_visitCount_pos_iff d root.2.1).2 ⟨0, root.2.2.1⟩
  exact (Nat.ne_of_gt hpos) hvisit.symm

theorem ons_decRootedExponentEquivUnboundedTuples_weight
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hk : 0 < m s(d, ons_dartRev L d))
    (root : {root : ons_DecRootedAtom L d //
      ons_decRootedAtomExponent root = m}) :
    ons_decRootedAtomWeight L a b root.1 =
      ∏ i, ons_decFirstReturnAtomWeight L a b
        ((ons_decRootedExponentEquivUnboundedTuples L d m hk root).1 i) := by
  let atoms := (ons_decRootedAtomEquivNonemptyAtoms L d root.1).1
  let tuple :=
    (ons_decRootedExponentEquivUnboundedTuples L d m hk root).1
  have hlength : atoms.length = m s(d, ons_dartRev L d) := by
    rw [ons_decRootedAtom_atoms_length_eq_visitCount L d root.1,
      ← ons_decRootedAtom_externalExponent_eq_visitCount L d root.1,
      root.2]
  let atomVector : {atoms : List (ons_DecFirstReturnAtom L d) //
      atoms.length = m s(d, ons_dartRev L d)} := ⟨atoms, hlength⟩
  have htuple : tuple =
      ons_listLengthEquivTuple (m s(d, ons_dartRev L d)) atomVector := by
    rfl
  have hlist : List.ofFn tuple = atoms := by
    rw [htuple]
    exact congrArg Subtype.val
      ((ons_listLengthEquivTuple (m s(d, ons_dartRev L d))).symm_apply_apply
        atomVector)
  rw [ons_decRootedAtomWeight_eq_atoms_prod]
  change (atoms.map (ons_decFirstReturnAtomWeight L a b)).prod = _
  rw [← hlist, List.map_ofFn, List.prod_ofFn]
  rfl

theorem ons_decBoundedRootEquivBoundedTuples_weight_div
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hk : 0 < m s(d, ons_dartRev L d))
    (root : {root : ons_DecRootedAtomBounded L d
        (ons_finsuppTotalDegree m) //
      ons_decBoundedRootExponent root = m}) :
    ons_decBoundedRootWeight L a b root.1 /
        (ons_visitCount d root.1.2.1 : ℂ) =
      (∏ i, ons_decBoundedAtomWeight L a b
        ((ons_decBoundedRootEquivBoundedTuples L d m hk root).1 i)) /
          (m s(d, ons_dartRev L d) : ℂ) := by
  let unboundedRoot := ons_decBoundedRootEquivUnbounded L d m root
  let unboundedTuple :=
    ons_decRootedExponentEquivUnboundedTuples L d m hk unboundedRoot
  let boundedTuple :=
    ons_decBoundedRootEquivBoundedTuples L d m hk root
  have htupleSubtype :=
    (ons_decBoundedTupleEquivUnbounded L d m).apply_symm_apply
      unboundedTuple
  have htuple :
      (∀ i, ons_decForgetBoundedAtom (boundedTuple.1 i) =
        unboundedTuple.1 i) := by
    intro i
    exact congrFun (congrArg Subtype.val htupleSubtype) i
  have hweight := ons_decRootedExponentEquivUnboundedTuples_weight
    L a b d m hk unboundedRoot
  have hweight' : ons_decBoundedRootWeight L a b root.1 =
      ∏ i, ons_decBoundedAtomWeight L a b (boundedTuple.1 i) := by
    change ons_decRootedAtomWeight L a b unboundedRoot.1 = _
    rw [hweight]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← htuple i, ons_decForgetBoundedAtom_weight]
  have hvisit := ons_decRootedAtom_externalExponent_eq_visitCount
    L d unboundedRoot.1
  have hvisit' : ons_visitCount d root.1.2.1 =
      m s(d, ons_dartRev L d) := by
    change ons_decBoundedRootExponent root.1 s(d, ons_dartRev L d) =
      ons_visitCount d root.1.2.1 at hvisit
    rw [root.2] at hvisit
    exact hvisit.symm
  rw [hweight', hvisit']

theorem ons_decFormalRootedLogCoeff_eq_neg_coeff_pow_div
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hk : 0 < m s(d, ons_dartRev L d)) :
    ons_decFormalRootedLogCoeff L a b d m =
      -(MvPowerSeries.coeff m
          (ons_decFormalFirstReturn L a b d ^
            m s(d, ons_dartRev L d)) /
        (m s(d, ons_dartRev L d) : ℂ)) := by
  classical
  rw [ons_decFormalRootedLogCoeff_eq_boundedRootSum,
    ons_decFormalFirstReturn_coeff_pow_eq_boundedTupleSum]
  apply congrArg Neg.neg
  let rootEquiv := ons_decBoundedRootEquivBoundedTuples L d m hk
  calc
    (∑ root : ons_DecRootedAtomBounded L d
        (ons_finsuppTotalDegree m),
      if ons_decBoundedRootExponent root = m then
        ons_decBoundedRootWeight L a b root /
          (ons_visitCount d root.2.1 : ℂ)
      else 0) =
      ∑ root : {root : ons_DecRootedAtomBounded L d
          (ons_finsuppTotalDegree m) //
        ons_decBoundedRootExponent root = m},
        ons_decBoundedRootWeight L a b root.1 /
          (ons_visitCount d root.1.2.1 : ℂ) := by
            rw [← Finset.sum_subtype
              (s := Finset.univ.filter
                (fun root : ons_DecRootedAtomBounded L d
                    (ons_finsuppTotalDegree m) ↦
                  ons_decBoundedRootExponent root = m))
              (by simp)
              (fun root ↦ ons_decBoundedRootWeight L a b root /
                (ons_visitCount d root.2.1 : ℂ)),
              Finset.sum_filter]
    _ = ∑ atoms : {atoms : Fin (m s(d, ons_dartRev L d)) →
          ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m) //
        (∑ i, ons_decBoundedAtomExponent (atoms i)) = m},
        (∏ i, ons_decBoundedAtomWeight L a b (atoms.1 i)) /
          (m s(d, ons_dartRev L d) : ℂ) := by
            apply Fintype.sum_equiv rootEquiv
            intro root
            exact ons_decBoundedRootEquivBoundedTuples_weight_div
              L a b d m hk root
    _ = (∑ atoms : Fin (m s(d, ons_dartRev L d)) →
          ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m),
        if (∑ i, ons_decBoundedAtomExponent (atoms i)) = m then
          ∏ i, ons_decBoundedAtomWeight L a b (atoms i)
        else 0) / (m s(d, ons_dartRev L d) : ℂ) := by
            rw [← Finset.sum_div]
            apply congrArg (fun z : ℂ ↦
              z / (m s(d, ons_dartRev L d) : ℂ))
            rw [← Finset.sum_subtype
              (s := Finset.univ.filter
                (fun atoms : Fin (m s(d, ons_dartRev L d)) →
                    ons_DecFirstReturnAtomBounded L d
                      (ons_finsuppTotalDegree m) ↦
                  (∑ i, ons_decBoundedAtomExponent (atoms i)) = m))
              (by simp)
              (fun atoms ↦
                ∏ i, ons_decBoundedAtomWeight L a b (atoms i)),
              Finset.sum_filter]

theorem ons_decBoundedAtom_externalExponent
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) {N : ℕ}
    (atom : ons_DecFirstReturnAtomBounded L d N) :
    ons_decBoundedAtomExponent atom s(d, ons_dartRev L d) = 1 :=
  ons_decLoopExponent_external_eq_one_of_firstReturn
    L d atom.2.1 atom.2.2

theorem ons_decFormalFirstReturn_coeff_pow_eq_zero_of_ne_external
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) (k : ℕ)
    (hne : k ≠ m s(d, ons_dartRev L d)) :
    MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d ^ k) = 0 := by
  classical
  rw [ons_decFormalFirstReturn_coeff_pow_eq_boundedTupleSum]
  apply Finset.sum_eq_zero
  intro atoms hatoms
  rw [if_neg]
  intro hexponent
  apply hne
  have happ := congrArg
    (fun exponent : ons_DecEdge L →₀ ℕ ↦
      exponent s(d, ons_dartRev L d)) hexponent
  simp only [Finsupp.finsetSum_apply,
    ons_decBoundedAtom_externalExponent] at happ
  simpa using happ

theorem ons_decFormalFirstReturn_neg_coeff_pow
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) (k : ℕ) :
    MvPowerSeries.coeff m ((-ons_decFormalFirstReturn L a b d) ^ k) =
      (-1 : ℂ) ^ k *
        MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d ^ k) := by
  rw [show -ons_decFormalFirstReturn L a b d =
      (-1 : ℂ) • ons_decFormalFirstReturn L a b d by simp,
    smul_pow, MvPowerSeries.coeff_smul]

theorem ons_decFormalFirstReturn_neg_hasSubst
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    PowerSeries.HasSubst (-ons_decFormalFirstReturn L a b d) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  rw [map_neg, ons_decFormalFirstReturn_constantCoeff]
  simp

theorem ons_decFormalRootedLogCoeff_eq_log_subst
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    ons_decFormalRootedLogCoeff L a b d m =
      MvPowerSeries.coeff m
        (PowerSeries.subst (-ons_decFormalFirstReturn L a b d)
          (PowerSeries.log ℂ)) := by
  classical
  rw [PowerSeries.coeff_subst
    (ons_decFormalFirstReturn_neg_hasSubst L a b d)]
  let k := m s(d, ons_dartRev L d)
  by_cases hk : k = 0
  · have hroot := ons_decFormalRootedLogCoeff_eq_zero_of_external_zero
      L a b d m hk
    rw [hroot]
    rw [← finsum_zero]
    apply finsum_congr
    intro n
    by_cases hn : n = 0
    · subst n
      rw [PowerSeries.coeff_log]
      simp
    · have hne : n ≠ m s(d, ons_dartRev L d) := by
        change n ≠ k
        rw [hk]
        exact hn
      rw [ons_decFormalFirstReturn_neg_coeff_pow,
        ons_decFormalFirstReturn_coeff_pow_eq_zero_of_ne_external
          L a b d m n hne, mul_zero, smul_zero]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    rw [finsum_eq_single _ k]
    · rw [ons_decFormalRootedLogCoeff_eq_neg_coeff_pow_div
          L a b d m hkpos,
        PowerSeries.coeff_log, if_neg hk,
        ons_decFormalFirstReturn_neg_coeff_pow]
      change -(MvPowerSeries.coeff m
          (ons_decFormalFirstReturn L a b d ^ k) / (k : ℂ)) =
        (algebraMap ℚ ℂ) ((-1 : ℚ) ^ (k + 1) / (k : ℚ)) •
          ((-1 : ℂ) ^ k * MvPowerSeries.coeff m
            (ons_decFormalFirstReturn L a b d ^ k))
      push_cast
      have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      have hsign : (-1 : ℂ) ^ (k + 1) * (-1 : ℂ) ^ k = -1 := by
        rw [← pow_add]
        have heven : Even (k + k) := ⟨k, by omega⟩
        rw [show k + 1 + k = (k + k) + 1 by omega,
          pow_succ, heven.neg_one_pow]
        ring
      let c := MvPowerSeries.coeff m
        (ons_decFormalFirstReturn L a b d ^ k)
      change -(c / (k : ℂ)) =
        ((-1 : ℂ) ^ (k + 1) / (k : ℂ)) *
          ((-1 : ℂ) ^ k * c)
      calc
        -(c / (k : ℂ)) = (-1 : ℂ) * c / (k : ℂ) := by ring
        _ = (((-1 : ℂ) ^ (k + 1) * (-1 : ℂ) ^ k) * c) /
            (k : ℂ) := by rw [hsign]
        _ = ((-1 : ℂ) ^ (k + 1) / (k : ℂ)) *
            ((-1 : ℂ) ^ k * c) := by
              field_simp [hkC]
    · intro n hnk
      have hzero := ons_decFormalFirstReturn_coeff_pow_eq_zero_of_ne_external
        L a b d m n (by simpa only [k] using hnk)
      rw [ons_decFormalFirstReturn_neg_coeff_pow, hzero,
        mul_zero, smul_zero]

theorem ons_decFormalRootedLog_eq_log_subst
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    ons_decFormalRootedLog L a b d =
      PowerSeries.subst (-ons_decFormalFirstReturn L a b d)
        (PowerSeries.log ℂ) := by
  ext m
  exact ons_decFormalRootedLogCoeff_eq_log_subst L a b d m

theorem ons_powerSeries_deriv_deriv_log :
    PowerSeries.derivative ℂ
        (PowerSeries.derivative ℂ (PowerSeries.log ℂ)) =
      -((PowerSeries.derivative ℂ (PowerSeries.log ℂ)) ^ 2) := by
  open PowerSeries in
    rw [deriv_log]
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, map_neg,
    pow_two, PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  have hsum : (∑ p ∈ Finset.antidiagonal n,
      (algebraMap ℚ ℂ) ((-1 : ℚ) ^ p.1) *
        (algebraMap ℚ ℂ) ((-1 : ℚ) ^ p.2)) =
      (n + 1 : ℂ) * ((-1 : ℂ) ^ n) := by
    calc
      _ = ∑ p ∈ Finset.antidiagonal n, ((-1 : ℂ) ^ n) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [← map_mul, ← pow_add, Finset.mem_antidiagonal.mp hp]
        simp
      _ = _ := by simp
  rw [hsum]
  push_cast
  rw [pow_succ]
  ring

theorem ons_powerSeries_exp_log :
    PowerSeries.subst (PowerSeries.log ℂ) (PowerSeries.exp ℂ) =
      1 + PowerSeries.X := by
  let F := PowerSeries.subst (PowerSeries.log ℂ) (PowerSeries.exp ℂ)
  let G := PowerSeries.derivative ℂ (PowerSeries.log ℂ)
  have hchain : PowerSeries.derivative ℂ F = F * G := by
    dsimp only [F, G]
    rw [PowerSeries.derivative_subst ℂ PowerSeries.HasSubst.log,
      PowerSeries.derivative_exp]
  have hG : PowerSeries.derivative ℂ G = -(G ^ 2) :=
    ons_powerSeries_deriv_deriv_log
  have hsecond :
      PowerSeries.derivative ℂ (PowerSeries.derivative ℂ F) = 0 := by
    calc
      PowerSeries.derivative ℂ (PowerSeries.derivative ℂ F) =
          PowerSeries.derivative ℂ (F * G) := by rw [hchain]
      _ = PowerSeries.derivative ℂ F * G +
          F * PowerSeries.derivative ℂ G := by
            simpa [smul_eq_mul, add_comm, mul_comm] using
              Derivation.leibniz (PowerSeries.derivative ℂ) F G
      _ = (F * G) * G + F * (-(G ^ 2)) := by rw [hchain, hG]
      _ = 0 := by ring
  have hcF : PowerSeries.constantCoeff F = 1 := by
    change MvPowerSeries.constantCoeff F = 1
    dsimp only [F]
    rw [PowerSeries.constantCoeff_subst PowerSeries.HasSubst.log]
    rw [finsum_eq_single _ 0]
    · simp
    · intro n hn
      have hclog : MvPowerSeries.constantCoeff (PowerSeries.log ℂ) = 0 := by
        exact PowerSeries.constantCoeff_log
      rw [map_pow, hclog, zero_pow hn, smul_zero]
  have hcG : PowerSeries.constantCoeff G = 1 := by
    dsimp only [G]
    rw [PowerSeries.deriv_log]
    simp
  have hcDF :
      PowerSeries.constantCoeff (PowerSeries.derivative ℂ F) = 1 := by
    rw [hchain, map_mul, hcF, hcG, mul_one]
  have hDF : PowerSeries.derivative ℂ F = 1 := by
    apply PowerSeries.derivative.ext
    · rw [hsecond]
      simp
    · rw [hcDF]
      simp
  change F = 1 + PowerSeries.X
  apply PowerSeries.derivative.ext
  · rw [hDF]
    simp
  · rw [hcF]
    simp

theorem ons_decFormalRootedExp_eq_one_sub_firstReturn
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    PowerSeries.subst (ons_decFormalRootedLog L a b d)
        (PowerSeries.exp ℂ) =
      1 - ons_decFormalFirstReturn L a b d := by
  rw [ons_decFormalRootedLog_eq_log_subst]
  rw [← PowerSeries.subst_comp_subst_apply
    PowerSeries.HasSubst.log
    (ons_decFormalFirstReturn_neg_hasSubst L a b d)]
  rw [ons_powerSeries_exp_log]
  rw [PowerSeries.subst_add
    (ons_decFormalFirstReturn_neg_hasSubst L a b d)]
  have hone : PowerSeries.subst (-ons_decFormalFirstReturn L a b d)
      (1 : PowerSeries ℂ) = 1 := by
    rw [← PowerSeries.coe_substAlgHom
      (ons_decFormalFirstReturn_neg_hasSubst L a b d)]
    exact map_one _
  rw [hone, PowerSeries.subst_X
    (ons_decFormalFirstReturn_neg_hasSubst L a b d)]
  ring

namespace DecFormalExpAdd

lemma fin2_exp (e : Fin 2 →₀ ℕ) :
    Finsupp.single (0 : Fin 2) (e 0) +
        Finsupp.single (1 : Fin 2) (e 1) = e := by
  ext i
  fin_cases i <;> simp

lemma ex_coeff (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
      (PowerSeries.subst (MvPowerSeries.X (0 : Fin 2))
        (PowerSeries.exp ℂ)) =
      if e 1 = 0 then (1 : ℂ) / (e 0).factorial else 0 := by
  rw [PowerSeries.coeff_subst_single, PowerSeries.coeff_exp]
  by_cases h : e 1 = 0
  · rw [if_pos h, if_pos]
    · push_cast
      rfl
    · ext i
      fin_cases i <;> simp [h]
  · rw [if_neg h, if_neg]
    intro he
    have he' := congrArg (fun x : Fin 2 →₀ ℕ ↦ x 1) he
    simp at he'
    exact h he'

lemma ey_coeff (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
      (PowerSeries.subst (MvPowerSeries.X (1 : Fin 2))
        (PowerSeries.exp ℂ)) =
      if e 0 = 0 then (1 : ℂ) / (e 1).factorial else 0 := by
  rw [PowerSeries.coeff_subst_single, PowerSeries.coeff_exp]
  by_cases h : e 0 = 0
  · rw [if_pos h, if_pos]
    · push_cast
      rfl
    · ext i
      fin_cases i <;> simp [h]
  · rw [if_neg h, if_neg]
    intro he
    have he' := congrArg (fun x : Fin 2 →₀ ℕ ↦ x 0) he
    simp at he'
    exact h he'

lemma prod_coeff (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
      (PowerSeries.subst (MvPowerSeries.X (0 : Fin 2))
          (PowerSeries.exp ℂ) *
        PowerSeries.subst (MvPowerSeries.X (1 : Fin 2))
          (PowerSeries.exp ℂ)) =
      (1 : ℂ) / ((e 0).factorial * (e 1).factorial) := by
  rw [MvPowerSeries.coeff_mul]
  let target : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) :=
    (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))
  rw [Finset.sum_eq_single target]
  · rw [ex_coeff, ey_coeff]
    simp [target]
    ring
  · rintro ⟨p, q⟩ hpq hne
    rw [ex_coeff, ey_coeff]
    by_cases hp : p 1 = 0
    · by_cases hq : q 0 = 0
      · exfalso
        apply hne
        have hadd := Finset.mem_antidiagonal.mp hpq
        dsimp only [target]
        apply Prod.ext
        · ext i
          fin_cases i
          · have hi := congrArg (fun x : Fin 2 →₀ ℕ ↦ x 0) hadd
            simp [hq] at hi ⊢
            exact hi
          · simp [hp]
        · ext i
          fin_cases i
          · simp [hq]
          · have hi := congrArg (fun x : Fin 2 →₀ ℕ ↦ x 1) hadd
            simp [hp] at hi ⊢
            exact hi
      · simp [hq]
    · simp [hp]
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.mem_antidiagonal]
    exact fin2_exp e

lemma add_coeff (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
      (PowerSeries.subst
        (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2))
        (PowerSeries.exp ℂ)) =
      (1 : ℂ) / ((e 0).factorial * (e 1).factorial) := by
  rw [PowerSeries.coeff_subst
    (PowerSeries.HasSubst.X 0 |>.add (PowerSeries.HasSubst.X 1))]
  rw [finsum_eq_single _ (e 0 + e 1)]
  · rw [PowerSeries.coeff_exp]
    have hcoe :
        (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) ^
            (e 0 + e 1) =
          (((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^
              (e 0 + e 1) : MvPolynomial (Fin 2) ℂ) :
            MvPowerSeries (Fin 2) ℂ) := by
      simp
    rw [hcoe, MvPolynomial.coeff_coe, MvPolynomial.coeff_add_pow]
    rw [if_pos]
    · simp only [smul_eq_mul]
      push_cast
      have hfac := Nat.choose_mul_factorial_mul_factorial
        (Nat.le_add_right (e 0) (e 1))
      rw [Nat.add_sub_cancel_left] at hfac
      have heq : ((e 0 + e 1).choose (e 0) : ℂ) *
          ((e 0).factorial : ℂ) * ((e 1).factorial : ℂ) =
          ((e 0 + e 1).factorial : ℂ) := by
        exact_mod_cast hfac
      have h0 : ((e 0).factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (e 0)
      have h1 : ((e 1).factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (e 1)
      have hs : ((e 0 + e 1).factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (e 0 + e 1)
      field_simp [h0, h1, hs]
      exact heq
    · rw [Finset.mem_antidiagonal]
  · intro n hn
    have hcoe :
        (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) ^ n =
          (((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ n :
              MvPolynomial (Fin 2) ℂ) : MvPowerSeries (Fin 2) ℂ) := by
      simp
    rw [hcoe, MvPolynomial.coeff_coe, MvPolynomial.coeff_add_pow]
    rw [if_neg]
    simp
    rw [Finset.mem_antidiagonal]
    exact fun h ↦ hn h.symm

lemma biv_exp :
    PowerSeries.subst
        (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ)
        (PowerSeries.exp ℂ) *
      PowerSeries.subst
        (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ)
        (PowerSeries.exp ℂ) =
      PowerSeries.subst
        ((MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) :
          MvPowerSeries (Fin 2) ℂ)
        (PowerSeries.exp ℂ) := by
  ext e
  rw [prod_coeff (e := e), add_coeff (e := e)]

end DecFormalExpAdd

theorem ons_powerSeries_subst_exp_add_of_constantCoeff_zero
    {τ : Type*} (A B : MvPowerSeries τ ℂ)
    (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) :
    PowerSeries.subst A (PowerSeries.exp ℂ) *
      PowerSeries.subst B (PowerSeries.exp ℂ) =
      PowerSeries.subst (A + B) (PowerSeries.exp ℂ) := by
  let v : Fin 2 → MvPowerSeries τ ℂ := ![A, B]
  have hv : MvPowerSeries.HasSubst v :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i ↦ by
      fin_cases i <;> simp [v, hA, hB])
  have h := congrArg (MvPowerSeries.subst v) DecFormalExpAdd.biv_exp
  rw [MvPowerSeries.subst_mul hv] at h
  have hX0 : MvPowerSeries.subst v
      (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ) = A := by
    rw [MvPowerSeries.subst_X hv]
    rfl
  have hX1 : MvPowerSeries.subst v
      (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ) = B := by
    rw [MvPowerSeries.subst_X hv]
    rfl
  have hXadd : MvPowerSeries.subst v
      ((MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) :
        MvPowerSeries (Fin 2) ℂ) = A + B := by
    rw [MvPowerSeries.subst_add hv, hX0, hX1]
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    PowerSeries.subst_def] at h
  have hv0 : MvPowerSeries.HasSubst
      (fun _ : Unit ↦
        (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ)) := by
    simpa only using
      (PowerSeries.hasSubst_iff.mp (PowerSeries.HasSubst.X (0 : Fin 2)))
  have hv1 : MvPowerSeries.HasSubst
      (fun _ : Unit ↦
        (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ)) := by
    simpa only using
      (PowerSeries.hasSubst_iff.mp (PowerSeries.HasSubst.X (1 : Fin 2)))
  have hvadd : MvPowerSeries.HasSubst
      (fun _ : Unit ↦
        ((MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) :
          MvPowerSeries (Fin 2) ℂ)) := by
    simpa only using PowerSeries.hasSubst_iff.mp
      ((PowerSeries.HasSubst.X (0 : Fin 2)).add
        (PowerSeries.HasSubst.X (1 : Fin 2)))
  rw [MvPowerSeries.subst_comp_subst_apply hv0 hv,
    MvPowerSeries.subst_comp_subst_apply hv1 hv,
    MvPowerSeries.subst_comp_subst_apply hvadd hv,
    hX0, hX1, hXadd] at h
  exact h

theorem ons_decFormalRootedLog_constantCoeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    MvPowerSeries.constantCoeff (ons_decFormalRootedLog L a b d) = 0 := by
  change ons_decFormalRootedLogCoeff L a b d 0 = 0
  apply ons_decFormalRootedLogCoeff_eq_zero_of_external_zero
  rfl

theorem ons_decFormalRoot_eq_avoidRoot_mul_one_sub_firstReturn
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    ons_decFormalRoot L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) =
      ons_decFormalAvoidRoot L a b d *
        (1 - ons_decFormalFirstReturn L a b d) := by
  unfold ons_decFormalRoot
  rw [ons_decFormalLog_eq_rooted_add_avoid L a b d]
  rw [← ons_powerSeries_subst_exp_add_of_constantCoeff_zero
    (ons_decFormalRootedLog L a b d)
    (ons_decFormalAvoidLog L a b d)
    (ons_decFormalRootedLog_constantCoeff L a b d)
    (ons_decFormalAvoidLog_constantCoeff L a b d)]
  rw [ons_decFormalRootedExp_eq_one_sub_firstReturn]
  unfold ons_decFormalAvoidRoot
  ring

theorem ons_one_sub_decFormalFirstReturn_coeff_eq_zero_of_external_ge_two
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hmedge : 1 < m s(d, ons_dartRev L d)) :
    MvPowerSeries.coeff m (1 - ons_decFormalFirstReturn L a b d) = 0 := by
  rw [map_sub]
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hmedge
  rw [MvPowerSeries.coeff_one, if_neg hm0]
  have hm1 : m s(d, ons_dartRev L d) ≠ 1 := by omega
  change 0 - ons_decFormalFirstReturnCoeff L a b d m = 0
  rw [ons_decFormalFirstReturnCoeff_eq_zero_unless_external_one
    L a b d m hm1]
  simp

theorem ons_decFormalRoot_coeff_eq_zero_of_external_ge_two
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hmedge : 1 < m s(d, ons_dartRev L d)) :
    MvPowerSeries.coeff m
      (ons_decFormalRoot L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
  classical
  rw [ons_decFormalRoot_eq_avoidRoot_mul_one_sub_firstReturn L a b d]
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨p, q⟩ hpq
  have hadd := congrArg (fun x : ons_DecEdge L →₀ ℕ ↦
    x s(d, ons_dartRev L d)) (Finset.mem_antidiagonal.mp hpq)
  simp only [Finsupp.add_apply] at hadd
  by_cases hp : p s(d, ons_dartRev L d) = 0
  · have hq : 1 < q s(d, ons_dartRev L d) := by omega
    rw [ons_one_sub_decFormalFirstReturn_coeff_eq_zero_of_external_ge_two
      L a b d q hq, mul_zero]
  · rw [ons_decFormalAvoidRoot_coeff_eq_zero_of_external
      L a b d p hp, zero_mul]

end StatMech.Onsager
