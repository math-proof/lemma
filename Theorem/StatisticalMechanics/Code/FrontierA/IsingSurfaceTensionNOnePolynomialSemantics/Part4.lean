/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneRawGenerated
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneLayerCode.Part2
import Std.Data.TreeMap.Lemmas
import Std.Data.DTreeMap.Internal.Lemmas
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics.Part3
open Finset
open Std
open scoped Std.DTreeMap.Internal.Impl


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

theorem evalXSquareDivisionInvariant_step
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (e : Int) (qr : BiPoly × BiPoly) :
    evalXSquareDivisionInvariant X Y
        (BiPoly.divXsqSubOneStep e qr) =
      evalXSquareDivisionInvariant X Y qr := by
  rcases qr with ⟨q, r⟩
  unfold BiPoly.divXsqSubOneStep evalXSquareDivisionInvariant
  dsimp only
  let qadd := (r.leadingX e).mapExponent fun ex ey => (ex - 2, ey)
  let factor : BiPoly := .ofTerms
    [{ ex := 2, ey := 0, coeff := 1 },
      { ex := 0, ey := 0, coeff := -1 }]
  change (q.add qadd).eval X Y * (X ^ 2 - 1) +
      (r.sub (qadd.mul factor)).eval X Y =
    q.eval X Y * (X ^ 2 - 1) + r.eval X Y
  have ha := BiPoly.eval_add X Y q qadd
  change (q.add qadd).eval X Y = q.eval X Y + qadd.eval X Y at ha
  have hs := BiPoly.eval_sub X Y r (qadd.mul factor)
  change (r.sub (qadd.mul factor)).eval X Y =
    r.eval X Y - (qadd.mul factor).eval X Y at hs
  have hm := BiPoly.eval_mul X Y hX hY qadd factor
  change (qadd.mul factor).eval X Y =
    qadd.eval X Y * factor.eval X Y at hm
  have hf : factor.eval X Y = X ^ 2 - 1 := by
    unfold factor
    rw [BiPoly.eval_ofTerms]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      BiTerm.eval]
    norm_num
    rfl
  rw [ha, hs, hm, hf]
  ring

theorem evalXSquareDivisionInvariant_foldl
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (es : List Int) (qr : BiPoly × BiPoly) :
    evalXSquareDivisionInvariant X Y
        (es.foldl (fun qr e => BiPoly.divXsqSubOneStep e qr) qr) =
      evalXSquareDivisionInvariant X Y qr := by
  induction es generalizing qr with
  | nil => rfl
  | cons e es ih =>
      rw [List.foldl_cons, ih,
        evalXSquareDivisionInvariant_step X Y hX hY]

theorem BiPoly.eval_divXsqSubOne
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (top : Nat) (p : BiPoly) :
    p.eval X Y =
      (p.divXsqSubOne top).1.eval X Y * (X ^ 2 - 1) +
        (p.divXsqSubOne top).2.eval X Y := by
  have h := evalXSquareDivisionInvariant_foldl X Y hX hY
    (descendingFrom top) (.monomial 0 0 0, p)
  unfold BiPoly.divXsqSubOne
  simpa [evalXSquareDivisionInvariant] using h.symm

theorem BiPoly.eval_eq_zero_of_isEmpty (X Y : Real) (p : BiPoly)
    (h : p.terms.isEmpty = true) :
    p.eval X Y = 0 := by
  have hp : p.terms = [] := by simpa using h
  unfold BiPoly.eval
  rw [hp]
  rfl

theorem eval_clearedSkewPolyOf_eq_factors_of_remainderCertificate
    (p : BiPoly) (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hcert : remainderCertificateOf p = true) :
    (clearedSkewPolyOf p).eval X Y =
      (quotientPolyOf p).eval X Y * (X ^ 2 - 1) * (Y ^ 2 - 1) := by
  let c := clearedSkewPolyOf p
  let yd := c.divYsqSubOne 34
  let xd := yd.1.divXsqSubOne 294
  unfold remainderCertificateOf at hcert
  have hrem := Bool.and_eq_true_iff.mp hcert
  have hry0 : (quotientRemainderYOf p).eval X Y = 0 :=
    BiPoly.eval_eq_zero_of_isEmpty X Y (quotientRemainderYOf p) hrem.1
  have hrx0 : (quotientRemainderXOf p).eval X Y = 0 :=
    BiPoly.eval_eq_zero_of_isEmpty X Y (quotientRemainderXOf p) hrem.2
  have hry : yd.2.eval X Y = 0 := by
    simpa only [quotientRemainderYOf, yd, c] using hry0
  have hrx : xd.2.eval X Y = 0 := by
    simpa only [quotientRemainderXOf, xd, yd, c] using hrx0
  have hy := BiPoly.eval_divYsqSubOne X Y hX hY 34 c
  have hx := BiPoly.eval_divXsqSubOne X Y hX hY 294 yd.1
  change c.eval X Y = yd.1.eval X Y * (Y ^ 2 - 1) +
    yd.2.eval X Y at hy
  change yd.1.eval X Y = xd.1.eval X Y * (X ^ 2 - 1) +
    xd.2.eval X Y at hx
  change c.eval X Y = xd.1.eval X Y * (X ^ 2 - 1) *
    (Y ^ 2 - 1)
  rw [hy, hry, add_zero, hx, hrx, add_zero]

theorem binomialListSum (C : Real) (n : Nat) :
    ((List.range (n + 1)).map fun a =>
      ((n.choose a : Nat) : Real) * C ^ a).sum = (1 + C) ^ n := by
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  calc
    (∑ x ∈ Finset.range (n + 1), (n.choose x : Real) * C ^ x) =
        ∑ x ∈ Finset.range (n + 1),
          C ^ x * 1 ^ (n - x) * (n.choose x : Real) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (C + 1) ^ n := (add_pow C 1 n).symm
    _ = (1 + C) ^ n := by rw [add_comm]

end StatMech.FrontierA.NOneSymmetricMeanCertificate
