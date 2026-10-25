/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusBaseSpin
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicPhase.Part6
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Onsager.BaseCase

@[simp] theorem triangularIntStep_opposite (a : Fin 6) :
    triangularIntStep (triangularTorusDirectionReverse a) =
      -triangularIntStep a := by
  fin_cases a <;> rfl

@[simp] theorem triangularIntStep_swap (a : Fin 6) :
    triangularIntStep (triangularSwapDirection a) =
      triangularSwapPoint (triangularIntStep a) := by
  fin_cases a <;> rfl

theorem triangularIntPos_opposite
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6) (i : Fin n) :
    triangularIntPos (fun k => triangularTorusDirectionReverse (d k)) i =
      -triangularIntPos d i := by
  unfold triangularIntPos
  simp only [triangularIntStep_opposite]
  exact Finset.sum_neg_distrib
    (s := Finset.univ.filter (fun k : Fin n => k < i))
    (fun k => triangularIntStep (d k))

theorem triangularIntPos_swap
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6) (i : Fin n) :
    triangularIntPos (fun k => triangularSwapDirection (d k)) i =
      triangularSwapPoint (triangularIntPos d i) := by
  unfold triangularIntPos
  simp_rw [triangularIntStep_swap]
  apply Prod.ext
  · simp only [triangularSwapPoint, Prod.fst_sum, Prod.snd_sum]
  · simp only [triangularSwapPoint, Prod.fst_sum, Prod.snd_sum]

theorem triangularPathDisplacement_ofFn_opposite
    {n : Nat} (d : Fin n -> Fin 6) :
    triangularPathDisplacement
        (List.ofFn (fun k => triangularTorusDirectionReverse (d k))) =
      -triangularPathDisplacement (List.ofFn d) := by
  rw [triangularPathDisplacement_ofFn,
    triangularPathDisplacement_ofFn]
  simp only [triangularIntStep_opposite]
  exact Finset.sum_neg_distrib (s := Finset.univ)
    (fun k => triangularIntStep (d k))

theorem triangularPathDisplacement_ofFn_swap
    {n : Nat} (d : Fin n -> Fin 6) :
    triangularPathDisplacement
        (List.ofFn (fun k => triangularSwapDirection (d k))) =
      triangularSwapPoint
        (triangularPathDisplacement (List.ofFn d)) := by
  rw [triangularPathDisplacement_ofFn,
    triangularPathDisplacement_ofFn]
  simp_rw [triangularIntStep_swap]
  apply Prod.ext
  · simp only [triangularSwapPoint, Prod.fst_sum, Prod.snd_sum]
  · simp only [triangularSwapPoint, Prod.fst_sum, Prod.snd_sum]

theorem triangularPeriodStateCoord_opposite
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6) (z : Nat × Fin n) :
    triangularPeriodStateCoord
        (fun k => triangularTorusDirectionReverse (d k)) z =
      -triangularPeriodStateCoord d z := by
  rw [triangularPeriodStateCoord, triangularPeriodStateCoord,
    triangularIntPos_opposite,
    triangularPathDisplacement_ofFn_opposite]
  apply Prod.ext <;> simp [Prod.smul_mk] <;> ring

theorem triangularPeriodStateCoord_swap
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6) (z : Nat × Fin n) :
    triangularPeriodStateCoord
        (fun k => triangularSwapDirection (d k)) z =
      triangularSwapPoint (triangularPeriodStateCoord d z) := by
  rw [triangularPeriodStateCoord, triangularPeriodStateCoord,
    triangularIntPos_swap, triangularPathDisplacement_ofFn_swap]
  apply Prod.ext <;> simp [triangularSwapPoint, Prod.smul_mk]

theorem triangularPeriodStateCoord_opposite_injective
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hinj : Function.Injective (triangularPeriodStateCoord d)) :
    Function.Injective (triangularPeriodStateCoord
      (fun k => triangularTorusDirectionReverse (d k))) := by
  intro x y hxy
  apply hinj
  have h := congrArg Neg.neg hxy
  simpa [triangularPeriodStateCoord_opposite] using h

theorem triangularPeriodStateCoord_swap_injective
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hinj : Function.Injective (triangularPeriodStateCoord d)) :
    Function.Injective (triangularPeriodStateCoord
      (fun k => triangularSwapDirection (d k))) := by
  intro x y hxy
  apply hinj
  have h := congrArg triangularSwapPoint hxy
  simpa [triangularPeriodStateCoord_swap, triangularSwapPoint] using h

theorem kwVectorTurnPhase_triangular_eq_exp_turnExponent
    (a b : Fin 6) (hne : b ≠ triangularTorusDirectionReverse a) :
    kwVectorTurnPhase (triangularIntVector a) (triangularIntVector b) =
      Complex.exp
        ((((triangularTorusTurnExponent a b : Int) : Real) *
          (Real.pi / 4) : Complex) * Complex.I / 2) := by
  unfold kwVectorTurnPhase kwAngleTurnPhase
  rw [triangularIntVector_arg, triangularIntVector_arg,
    triangularTorusDirectionAngle_turn a b hne]
  congr 1
  push_cast
  ring

theorem triangularTurnExponent_opposite
    (a b : Fin 6) (hne : b ≠ triangularTorusDirectionReverse a) :
    triangularTorusTurnExponent
        (triangularTorusDirectionReverse a)
        (triangularTorusDirectionReverse b) =
      triangularTorusTurnExponent a b := by
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionReverse,
      triangularTorusTurnExponent] at hne ⊢

theorem triangularTurnExponent_swap
    (a b : Fin 6) (hne : b ≠ triangularTorusDirectionReverse a) :
    triangularTorusTurnExponent
        (triangularSwapDirection a) (triangularSwapDirection b) =
      -triangularTorusTurnExponent a b := by
  fin_cases a <;> fin_cases b <;>
    simp [triangularSwapDirection, triangularTorusDirectionReverse,
      triangularTorusTurnExponent] at hne ⊢

theorem triangularSwapDirection_reverse (a : Fin 6) :
    triangularSwapDirection (triangularTorusDirectionReverse a) =
      triangularTorusDirectionReverse (triangularSwapDirection a) := by
  fin_cases a <;> rfl

theorem triangularSwapDirection_injective :
    Function.Injective triangularSwapDirection := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [triangularSwapDirection] at h ⊢

theorem triangularOppositeDirection_reverse (a : Fin 6) :
    triangularTorusDirectionReverse
        (triangularTorusDirectionReverse a) = a := by
  fin_cases a <;> rfl

theorem triangularDirection_nonbacktracking_opposite
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k)) :
    ∀ k,
      triangularTorusDirectionReverse (d (k + 1)) ≠
        triangularTorusDirectionReverse
          (triangularTorusDirectionReverse (d k)) := by
  intro k h
  rw [triangularOppositeDirection_reverse] at h
  exact hnb k (triangularOppositeDirection_reverse (d (k + 1)) ▸
    congrArg triangularTorusDirectionReverse h)

theorem triangularDirection_nonbacktracking_swap
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k)) :
    ∀ k,
      triangularSwapDirection (d (k + 1)) ≠
        triangularTorusDirectionReverse
          (triangularSwapDirection (d k)) := by
  intro k h
  rw [<- triangularSwapDirection_reverse] at h
  exact hnb k (triangularSwapDirection_injective h)

theorem triangularPhaseCycle_opposite
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k)) :
    kwVectorPhaseCycle
        ((List.ofFn (fun k => triangularTorusDirectionReverse (d k))).map
          triangularIntVector) =
      kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) := by
  rw [show (List.ofFn
      (fun k => triangularTorusDirectionReverse (d k))).map
        triangularIntVector =
      List.ofFn (fun k => triangularIntVector
        (triangularTorusDirectionReverse (d k))) by
          rw [List.map_ofFn]
          congr 1,
    show (List.ofFn d).map triangularIntVector =
      List.ofFn (fun k => triangularIntVector (d k)) by
        rw [List.map_ofFn]
        congr 1,
    kwVectorPhaseCycle_ofFn, kwVectorPhaseCycle_ofFn]
  unfold kwLoopPhaseProduct
  apply Finset.prod_congr rfl
  intro k hk
  have hnb' := triangularDirection_nonbacktracking_opposite d hnb k
  rw [kwVectorTurnPhase_triangular_eq_exp_turnExponent _ _ hnb',
    kwVectorTurnPhase_triangular_eq_exp_turnExponent _ _ (hnb k),
    triangularTurnExponent_opposite _ _ (hnb k)]

theorem triangularPhaseCycle_swap
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k)) :
    kwVectorPhaseCycle
        ((List.ofFn (fun k => triangularSwapDirection (d k))).map
          triangularIntVector) =
      (kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector))⁻¹ := by
  rw [show (List.ofFn (fun k => triangularSwapDirection (d k))).map
        triangularIntVector =
      List.ofFn (fun k => triangularIntVector
        (triangularSwapDirection (d k))) by
          rw [List.map_ofFn]
          congr 1,
    show (List.ofFn d).map triangularIntVector =
      List.ofFn (fun k => triangularIntVector (d k)) by
        rw [List.map_ofFn]
        congr 1,
    kwVectorPhaseCycle_ofFn, kwVectorPhaseCycle_ofFn]
  unfold kwLoopPhaseProduct
  rw [<- Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  have hnb' := triangularDirection_nonbacktracking_swap d hnb k
  rw [kwVectorTurnPhase_triangular_eq_exp_turnExponent _ _ hnb',
    kwVectorTurnPhase_triangular_eq_exp_turnExponent _ _ (hnb k),
    triangularTurnExponent_swap _ _ (hnb k)]
  rw [<- Complex.exp_neg]
  congr 1
  push_cast
  ring


theorem triangularPeriodicSimple_phaseCycle_eq_one_of_nonzero
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hinj : Function.Injective (triangularPeriodStateCoord d))
    (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k))
    (hne : (triangularPathDisplacement (List.ofFn d)).1 ≠ 0 ∨
      (triangularPathDisplacement (List.ofFn d)).2 ≠ 0) :
    kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) = 1 := by
  let D := triangularPathDisplacement (List.ofFn d)
  change D.1 ≠ 0 ∨ D.2 ≠ 0 at hne
  by_cases hxpos : 0 < D.1
  · exact triangularPeriodicSimple_phaseCycle_eq_one_of_pos_x d hinj hxpos
  by_cases hxneg : D.1 < 0
  · let dr : Fin n -> Fin 6 := fun k => triangularTorusDirectionReverse (d k)
    have hDr : 0 < (triangularPathDisplacement (List.ofFn dr)).1 := by
      rw [triangularPathDisplacement_ofFn_opposite]
      simpa [D] using neg_pos.mpr hxneg
    have hr := triangularPeriodicSimple_phaseCycle_eq_one_of_pos_x dr
      (triangularPeriodStateCoord_opposite_injective d hinj) hDr
    rw [triangularPhaseCycle_opposite d hnb] at hr
    exact hr
  have hxzero : D.1 = 0 := by omega
  have hyne : D.2 ≠ 0 := hne.resolve_left (not_ne_iff.mpr hxzero)
  let ds : Fin n -> Fin 6 := fun k => triangularSwapDirection (d k)
  have hinjs := triangularPeriodStateCoord_swap_injective d hinj
  by_cases hypos : 0 < D.2
  · have hDs : 0 < (triangularPathDisplacement (List.ofFn ds)).1 := by
      rw [triangularPathDisplacement_ofFn_swap]
      exact hypos
    have hs := triangularPeriodicSimple_phaseCycle_eq_one_of_pos_x ds hinjs hDs
    rw [triangularPhaseCycle_swap d hnb] at hs
    simpa using congrArg Inv.inv hs
  · have hyneg : D.2 < 0 := lt_of_le_of_ne (le_of_not_gt hypos) hyne
    let drs : Fin n -> Fin 6 :=
      fun k => triangularTorusDirectionReverse (ds k)
    have hDrs : 0 < (triangularPathDisplacement (List.ofFn drs)).1 := by
      rw [triangularPathDisplacement_ofFn_opposite,
        triangularPathDisplacement_ofFn_swap]
      simpa using neg_pos.mpr hyneg
    have hrs := triangularPeriodicSimple_phaseCycle_eq_one_of_pos_x drs
      (triangularPeriodStateCoord_opposite_injective ds hinjs) hDrs
    rw [triangularPhaseCycle_opposite ds
      (triangularDirection_nonbacktracking_swap d hnb),
      triangularPhaseCycle_swap d hnb] at hrs
    simpa using congrArg Inv.inv hrs

theorem exists_triangularTurnExponent_sum_eq_eight_mul_even_of_phase_one
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (hnonbacktracking : ∀ k,
      direction (k + 1) ≠ triangularTorusDirectionReverse (direction k))
    (hphase : kwVectorPhaseCycle
      ((List.ofFn direction).map triangularIntVector) = 1) :
    ∃ m : Int,
      (∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1))) = 8 * (2 * m) := by
  have hphaseLoop : kwLoopPhaseProduct
      (fun a b => kwAngleTurnPhase
        (triangularTorusDirectionAngle a)
        (triangularTorusDirectionAngle b)) direction = 1 := by
    have hvec : kwLoopPhaseProduct kwVectorTurnPhase
        (fun k => triangularIntVector (direction k)) = 1 := by
      rw [<- kwVectorPhaseCycle_ofFn]
      have hlist : List.ofFn (fun k => triangularIntVector (direction k)) =
          (List.ofFn direction).map triangularIntVector := by
        rw [List.map_ofFn]
        congr 1
      rw [hlist]
      exact hphase
    unfold kwLoopPhaseProduct at hvec ⊢
    simpa only [kwVectorTurnPhase_triangularIntVector] using hvec
  obtain ⟨winding, hturn⟩ :=
    kw_totalPrincipalTurn_eq_int_mul_two_pi
      triangularTorusDirectionAngle direction
  have hexpEq := kwLoopPhaseProduct_angleTurnPhase_eq_exp_sum
    triangularTorusDirectionAngle direction
  rw [hphaseLoop, hturn] at hexpEq
  have hexp : Complex.exp
      (((winding : Real) * Real.pi : Complex) * Complex.I) = 1 := by
    convert hexpEq.symm using 1 <;> push_cast <;> ring
  have hexp' : Complex.exp
      (((((winding : Real) * Real.pi) : Real) : Complex) * Complex.I) = 1 := by
    convert hexp using 1 <;> push_cast <;> ring
  rw [Complex.exp_ofReal_mul_I] at hexp'
  have hre := congrArg Complex.re hexp'
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero] at hre
  norm_num at hre
  rw [Real.cos_int_mul_pi] at hre
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' winding
  · have hsum :
        (∑ k, (triangularTorusDirectionAngle (direction (k + 1)) -
          triangularTorusDirectionAngle (direction k)).toReal : Real) =
        ((∑ k, triangularTorusTurnExponent
          (direction k) (direction (k + 1)) : Int) : Real) *
            (Real.pi / 4) := by
      rw [show (∑ k,
          (triangularTorusDirectionAngle (direction (k + 1)) -
            triangularTorusDirectionAngle (direction k)).toReal : Real) =
          ∑ k, (triangularTorusTurnExponent
            (direction k) (direction (k + 1)) : Real) *
              (Real.pi / 4) by
        apply Finset.sum_congr rfl
        intro k _
        exact triangularTorusDirectionAngle_turn _ _
          (hnonbacktracking k)]
      rw [<- Finset.sum_mul]
      norm_cast
    have hreal :
        (((∑ k, triangularTorusTurnExponent
          (direction k) (direction (k + 1)) : Int) : Real) *
            (Real.pi / 4)) =
          (winding : Real) * (2 * Real.pi) := hsum.symm.trans hturn
    have hcast :
        (((∑ k, triangularTorusTurnExponent
          (direction k) (direction (k + 1)) : Int) : Real)) =
          8 * (winding : Real) := by
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp at hreal ⊢
      nlinarith
    have hint :
        (∑ k, triangularTorusTurnExponent
          (direction k) (direction (k + 1))) = 8 * winding := by
      exact_mod_cast hcast
    refine ⟨m, ?_⟩
    rw [hint, hm]
  · have hodd : Odd winding := ⟨m, by omega⟩
    have hneg : (-1 : Real) ^ winding = -1 := hodd.neg_one_zpow
    rw [hneg] at hre
    norm_num at hre

theorem triangularPeriodStateCoord_eq_intPeriodicPos
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (z : Nat × Fin n) :
    triangularPeriodStateCoord d z =
      triangularIntPeriodicPos d ((z.1 : Int), z.2) := by
  rw [triangularPeriodStateCoord, triangularIntPeriodicPos,
    triangularPathDisplacement_ofFn]
  apply Prod.ext <;> simp [Prod.smul_mk] <;> ring

theorem triangularPeriodStateCoord_injective_of_intPeriodicPos
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hinj : Function.Injective (triangularIntPeriodicPos d)) :
    Function.Injective (triangularPeriodStateCoord d) := by
  intro z w hzw
  have hcoords :
      triangularIntPeriodicPos d ((z.1 : Int), z.2) =
        triangularIntPeriodicPos d ((w.1 : Int), w.2) :=
    (triangularPeriodStateCoord_eq_intPeriodicPos d z).symm.trans
      (hzw.trans (triangularPeriodStateCoord_eq_intPeriodicPos d w))
  have h := hinj hcoords
  have hfst : (z.1 : Int) = (w.1 : Int) := by
    simpa using congrArg Prod.fst h
  have hsnd : z.2 = w.2 := by
    simpa using congrArg Prod.snd h
  apply Prod.ext
  · exact_mod_cast hfst
  · exact hsnd


theorem triangularTorus_cyclePhaseProduct_eq_one_of_nonzeroHomology
    (L : Nat) [Fact (2 < L)]
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L)
      p.edges.toFinset ≠ 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1)
      (kwGraphCycleDartLoop p) = 1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  obtain ⟨mx, my, hdisplacement, hwind, hinjInt⟩ :=
    exists_triangularTorusCycle_nonzeroHomology_periodicLift L p hp hhom
  let direction : Fin p.darts.length -> Fin 6 :=
    fun k => (triangularTorusCycleNativeDart L p k).2
  have hinj : Function.Injective (triangularPeriodStateCoord direction) :=
    triangularPeriodStateCoord_injective_of_intPeriodicPos direction hinjInt
  have hnonzero :
      (triangularPathDisplacement (List.ofFn direction)).1 ≠ 0 ∨
        (triangularPathDisplacement (List.ofFn direction)).2 ≠ 0 := by
    rw [triangularPathDisplacement_ofFn, hdisplacement]
    have hL : (L : Int) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_trans (by decide : 0 < 2)
        (Fact.out : 2 < L)))
    rcases hwind with hx | hy
    · exact Or.inl (mul_ne_zero hL hx)
    · exact Or.inr (mul_ne_zero hL hy)
  have hnb : ∀ k,
      direction (k + 1) ≠ triangularTorusDirectionReverse (direction k) := by
    simpa only [direction, triangularTorusCycleNativeDart_snd] using
      triangularTorus_cycleDirection_nonbacktracking L p hp
  have hprincipal := triangularPeriodicSimple_phaseCycle_eq_one_of_nonzero
    direction hinj hnb hnonzero
  obtain ⟨m, hm⟩ :=
    exists_triangularTurnExponent_sum_eq_eight_mul_even_of_phase_one
      direction hnb hprincipal
  apply triangularTorus_cyclePhaseProduct_eq_one_of_even_revolutions
    L rho hrho p hp m
  simpa only [direction, triangularTorusCycleNativeDart_snd] using hm

theorem triangularTorus_baseSpinSign_eq_if_homology_zero
    (h : SurfaceHomology 1) :
    (surfaceParitySign
      (surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0) h) : Complex) =
      if h = 0 then 1 else -1 := by
  rcases h with ⟨hx, hy⟩
  let x : Fin 2 := hx 0
  let y : Fin 2 := hy 0
  have hx' : hx = fun _ : Fin 1 => x := by
    funext i
    fin_cases i
    rfl
  have hy' : hy = fun _ : Fin 1 => y := by
    funext i
    fin_cases i
    rfl
  rw [hx', hy']
  rw [triangularTorusSurfaceSpin_zero_zero_sign]
  have hpair :
      ((fun _ : Fin 1 => x), (fun _ : Fin 1 => y)) = 0 ↔
        x = 0 ∧ y = 0 := by
    constructor
    · intro h
      constructor
      · simpa using congrArg (fun z => z.1 0) h
      · simpa using congrArg (fun z => z.2 0) h
    · rintro ⟨hx0, hy0⟩
      apply Prod.ext <;> funext i
      · simpa [hx0]
      · simpa [hy0]
  by_cases hxy : x = 0 ∧ y = 0
  · rw [if_pos hxy, if_pos (hpair.mpr hxy)]
  · rw [if_neg hxy, if_neg (fun h => hxy (hpair.mp h))]

end StatMech.FrontierA
