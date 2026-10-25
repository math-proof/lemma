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
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics.Part2
open Finset
open Std
open scoped Std.DTreeMap.Internal.Impl


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

theorem evalYSquareDivisionInvariant_step
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (e : Int) (qr : BiPoly × BiPoly) :
    evalYSquareDivisionInvariant X Y
        (BiPoly.divYsqSubOneStep e qr) =
      evalYSquareDivisionInvariant X Y qr := by
  rcases qr with ⟨q, r⟩
  unfold BiPoly.divYsqSubOneStep evalYSquareDivisionInvariant
  dsimp only
  let qadd := (r.leadingY e).mapExponent fun ex ey => (ex, ey - 2)
  let factor : BiPoly := .ofTerms
    [{ ex := 0, ey := 2, coeff := 1 },
      { ex := 0, ey := 0, coeff := -1 }]
  change (q.add qadd).eval X Y * (Y ^ 2 - 1) +
      (r.sub (qadd.mul factor)).eval X Y =
    q.eval X Y * (Y ^ 2 - 1) + r.eval X Y
  have ha := BiPoly.eval_add X Y q qadd
  change (q.add qadd).eval X Y = q.eval X Y + qadd.eval X Y at ha
  have hs := BiPoly.eval_sub X Y r (qadd.mul factor)
  change (r.sub (qadd.mul factor)).eval X Y =
    r.eval X Y - (qadd.mul factor).eval X Y at hs
  have hm := BiPoly.eval_mul X Y hX hY qadd factor
  change (qadd.mul factor).eval X Y =
    qadd.eval X Y * factor.eval X Y at hm
  have hf : factor.eval X Y = Y ^ 2 - 1 := by
    unfold factor
    rw [BiPoly.eval_ofTerms]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      BiTerm.eval]
    norm_num
    rfl
  rw [ha, hs, hm, hf]
  ring

theorem evalYSquareDivisionInvariant_foldl
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (es : List Int) (qr : BiPoly × BiPoly) :
    evalYSquareDivisionInvariant X Y
        (es.foldl (fun qr e => BiPoly.divYsqSubOneStep e qr) qr) =
      evalYSquareDivisionInvariant X Y qr := by
  induction es generalizing qr with
  | nil => rfl
  | cons e es ih =>
      rw [List.foldl_cons, ih,
        evalYSquareDivisionInvariant_step X Y hX hY]

theorem BiPoly.eval_divYsqSubOne
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (top : Nat) (p : BiPoly) :
    p.eval X Y =
      (p.divYsqSubOne top).1.eval X Y * (Y ^ 2 - 1) +
        (p.divYsqSubOne top).2.eval X Y := by
  have h := evalYSquareDivisionInvariant_foldl X Y hX hY
    (descendingFrom top) (.monomial 0 0 0, p)
  unfold BiPoly.divYsqSubOne
  simpa [evalYSquareDivisionInvariant] using h.symm

end StatMech.FrontierA.NOneSymmetricMeanCertificate
