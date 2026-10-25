/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.EvenSubgraphDecomp
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenPeel.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising


theorem kwStarTransition_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x : Sym2 (Unit ⊕ ι) -> ℂ}
    {phase : kwStarDart ι -> kwStarDart ι -> ℂ}
    {d1 d2 : kwStarDart ι} (h : kwStarTransition x phase d2 d1 ≠ 0) :
    kwStarDartHead d1 = kwStarDartTail d2 ∧
      kwStarDartHead d2 ≠ kwStarDartTail d1 := by
  by_contra hbad
  rcases d1 with ⟨leaf1, direction1⟩
  rcases d2 with ⟨leaf2, direction2⟩
  cases direction1 <;> cases direction2
  all_goals simp [kwStarTransition, kwStarDartHead, kwStarDartTail] at h hbad
  grind


theorem kwStarTransition_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Sym2 (Unit ⊕ ι) -> ℂ)
    (phase : kwStarDart ι -> kwStarDart ι -> ℂ) :
    kwStarTransition x phase ^ 2 = 0 := by
  rw [pow_two]
  ext d2 d1
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro d hd
  cases hdirection : d.2 <;> simp [kwStarTransition, hdirection]


theorem kwStarTransition_isNilpotent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Sym2 (Unit ⊕ ι) -> ℂ)
    (phase : kwStarDart ι -> kwStarDart ι -> ℂ) :
    IsNilpotent (kwStarTransition x phase) :=
  ⟨2, kwStarTransition_sq x phase⟩


theorem det_one_sub_eq_one_of_isNilpotent {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι ℂ) (hM : IsNilpotent M) :
    (1 - M).det = 1 := by
  have hpow : ∀ n : ℕ, (M ^ n).toLin' = M.toLin' ^ n := by
    intro n
    induction n with
    | zero => simp [Matrix.toLin'_one, Module.End.one_eq_id]
    | succ n ih =>
        rw [pow_succ, Matrix.toLin'_mul, ih, pow_succ, Module.End.mul_eq_comp]
  have hlin : IsNilpotent M.toLin' := by
    obtain ⟨n, hn⟩ := hM
    refine ⟨n, ?_⟩
    rw [<- hpow, hn]
    ext
    simp
  have hchar := hlin.charpoly_eq_X_pow_finrank
  rw [Matrix.charpoly_toLin'] at hchar
  have heval := Matrix.eval_charpoly M 1
  rw [hchar] at heval
  simpa using heval.symm


theorem kwStarTransition_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Sym2 (Unit ⊕ ι) -> ℂ)
    (phase : kwStarDart ι -> kwStarDart ι -> ℂ) :
    (1 - kwStarTransition x phase).det = 1 :=
  det_one_sub_eq_one_of_isNilpotent _ (kwStarTransition_isNilpotent x phase)


theorem kacWard_star {ι : Type} [Fintype ι] [DecidableEq ι]
    (x : Sym2 (Unit ⊕ ι) -> ℂ)
    (phase : kwStarDart ι -> kwStarDart ι -> ℂ) :
    (1 - kwStarTransition x phase).det = (kwEvenPolynomial (kwStarGraph ι) x) ^ 2 := by
  have hpoly : kwEvenPolynomial (kwStarGraph ι) x = 1 :=
    kwEvenPolynomial_eq_one_of_isAcyclic (kwStarGraph ι) (kwStarGraph_isAcyclic ι) x
  rw [kwStarTransition_det, hpoly]
  norm_num

end StatMech.FrontierA
