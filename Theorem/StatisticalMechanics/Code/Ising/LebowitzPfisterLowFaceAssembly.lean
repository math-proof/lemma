/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly
open Finset


namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

lemma evalTerms_insert (t : TriTerm) (ts : List TriTerm) (x y z : Real) :
    evalTerms (TriPoly.insert t ts) x y z =
      t.eval x y z + evalTerms ts x y z := by
  induction ts with
  | nil => simp [TriPoly.insert, evalTerms]
  | cons s ss ih =>
      simp only [TriPoly.insert]
      split_ifs with h
      · rcases h with ⟨hx, hy, hz⟩
        simp only [evalTerms, TriTerm.eval]
        rw [hx, hy, hz]
        push_cast
        ring
      · simp [evalTerms, ih]
        ring

lemma evalTerms_foldl_insert (out ts : List TriTerm) (x y z : Real) :
    evalTerms (ts.foldl (fun acc t => TriPoly.insert t acc) out) x y z =
      evalTerms out x y z + evalTerms ts x y z := by
  induction ts generalizing out with
  | nil => simp [evalTerms]
  | cons t ts ih =>
      rw [List.foldl_cons, ih, evalTerms_insert]
      simp [evalTerms]
      ring

@[simp] lemma eval_ofTerms (ts : List TriTerm) (x y z : Real) :
    (TriPoly.ofTerms ts).eval x y z = evalTerms ts x y z := by
  simp [TriPoly.eval, TriPoly.ofTerms, evalTerms_foldl_insert, evalTerms]

@[simp] lemma eval_const (q : Int) (x y z : Real) :
    (TriPoly.const q).eval x y z = q := by
  simp [TriPoly.const, TriPoly.eval, evalTerms, TriTerm.eval]

lemma evalTerms_negMap (ts : List TriTerm) (x y z : Real) :
    evalTerms (ts.map fun t => { t with coeff := -t.coeff }) x y z =
      -evalTerms ts x y z := by
  induction ts with
  | nil => norm_num [evalTerms]
  | cons t ts ih =>
      simp [evalTerms, TriTerm.eval, ih]
      ring

@[simp] lemma eval_neg (p : TriPoly) (x y z : Real) :
    (-p).eval x y z = -p.eval x y z := by
  exact evalTerms_negMap p.terms x y z

lemma evalTerms_append (ps qs : List TriTerm) (x y z : Real) :
    evalTerms (ps ++ qs) x y z =
      evalTerms ps x y z + evalTerms qs x y z := by
  induction ps with
  | nil => simp [evalTerms]
  | cons t ts ih => simp [evalTerms, ih]; ring

@[simp] lemma eval_add (p q : TriPoly) (x y z : Real) :
    (p + q).eval x y z = p.eval x y z + q.eval x y z := by
  rw [show p + q = TriPoly.ofTerms (p.terms ++ q.terms) from rfl, eval_ofTerms]
  exact evalTerms_append p.terms q.terms x y z

@[simp] lemma eval_sub (p q : TriPoly) (x y z : Real) :
    (p - q).eval x y z = p.eval x y z - q.eval x y z := by
  change (p + -q).eval x y z = _
  rw [eval_add, eval_neg]
  rfl

@[simp] lemma eval_zero (x y z : Real) :
    (0 : TriPoly).eval x y z = 0 := by
  rw [show (0 : TriPoly) = TriPoly.const 0 by rfl, eval_const]
  norm_num

@[simp] lemma eval_one (x y z : Real) :
    (1 : TriPoly).eval x y z = 1 := by
  rw [show (1 : TriPoly) = TriPoly.const 1 by rfl, eval_const]
  norm_num

@[simp] lemma eval_two (x y z : Real) :
    (2 : TriPoly).eval x y z = 2 := by
  rw [show (2 : TriPoly) = TriPoly.const 2 by rfl, eval_const]
  norm_num

@[simp] lemma eval_three (x y z : Real) :
    (3 : TriPoly).eval x y z = 3 := by
  rw [show (3 : TriPoly) = TriPoly.const 3 by rfl, eval_const]
  norm_num

@[simp] lemma eval_six (x y z : Real) :
    (6 : TriPoly).eval x y z = 6 := by
  rw [show (6 : TriPoly) = TriPoly.const 6 by rfl, eval_const]
  norm_num

@[simp] lemma eval_nine (x y z : Real) :
    (9 : TriPoly).eval x y z = 9 := by
  rw [show (9 : TriPoly) = TriPoly.const 9 by rfl, eval_const]
  norm_num

@[simp] lemma eval_1764 (x y z : Real) :
    (1764 : TriPoly).eval x y z = 1764 := by
  rw [show (1764 : TriPoly) = TriPoly.const 1764 by rfl, eval_const]
  norm_num

lemma evalTerms_mulMap (s : TriTerm) (ts : List TriTerm) (x y z : Real) :
    evalTerms (ts.map fun t =>
      { ex := s.ex + t.ex, ey := s.ey + t.ey, ez := s.ez + t.ez,
        coeff := s.coeff * t.coeff }) x y z =
      s.eval x y z * evalTerms ts x y z := by
  induction ts with
  | nil => simp [evalTerms]
  | cons t ts ih =>
      simp [evalTerms, TriTerm.eval, ih, pow_add]
      ring

lemma evalTerms_mulFlatMap (ss ts : List TriTerm) (x y z : Real) :
    evalTerms (ss.flatMap fun s => ts.map fun t =>
      { ex := s.ex + t.ex, ey := s.ey + t.ey, ez := s.ez + t.ez,
        coeff := s.coeff * t.coeff }) x y z =
      evalTerms ss x y z * evalTerms ts x y z := by
  induction ss with
  | nil => simp [evalTerms]
  | cons s ss ih =>
      rw [List.flatMap_cons, evalTerms_append, evalTerms_mulMap, ih]
      rw [evalTerms]
      ring

@[simp] lemma eval_mul (p q : TriPoly) (x y z : Real) :
    (p * q).eval x y z = p.eval x y z * q.eval x y z := by
  rw [show p * q = TriPoly.ofTerms (p.terms.flatMap fun s =>
    q.terms.map fun t =>
      { ex := s.ex + t.ex, ey := s.ey + t.ey, ez := s.ez + t.ez,
        coeff := s.coeff * t.coeff }) from rfl,
    eval_ofTerms, evalTerms_mulFlatMap]
  rfl

@[simp] lemma eval_pow (p : TriPoly) (n : Nat) (x y z : Real) :
    (p ^ n).eval x y z = p.eval x y z ^ n := by
  induction n with
  | zero =>
      change (TriPoly.const 1).eval x y z = 1
      simpa only [Int.cast_one] using eval_const 1 x y z
  | succ n ih =>
      rw [show p ^ (n + 1) = p * p ^ n from rfl, eval_mul, ih, pow_succ]
      ring

end LowFaceCertificate
end
end StatMech.Ising
