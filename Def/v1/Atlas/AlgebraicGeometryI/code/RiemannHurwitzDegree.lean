/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzFormula
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitzFormula
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
import Structure.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzDegree


noncomputable section

open RiemannHurwitzFormula CanonicalSheafCurves

namespace RiemannHurwitzDegree

/-- Convenience constructor for `CurveCoverData` from a source and target curve,
a degree `n`, a ramification degree `degR`, and the hypothesis that the genus
form of Riemann–Hurwitz holds. -/
def CurveCoverData.mk' (X Y : SmoothCompleteCurve) (n degR : ℤ)
    (h_nonneg : 0 ≤ degR)
    (h_pos : 0 < n)
    (_h_RH : 2 * X.g - 2 = n * (2 * Y.g - 2) + degR) :
    CurveCoverData where
  morphism := {
    degree := n
    deg_KX := X.degK
    deg_KY := Y.degK
    deg_R := degR
    h_deg_R_nonneg := h_nonneg
    h_deg_pos := h_pos
  }
  source := X
  target := Y
  h_degK_X := rfl
  h_degK_Y := rfl

/-- A double cover of `ℙ¹` by an elliptic curve (genus 1) with 4 simple
ramification points; the standard example. -/
def ellipticCoverP1 : CurveCoverData :=
  CurveCoverData.mk' (mkCurve 1) (mkCurve 0) 2 4
    (by norm_num)
    (by norm_num)
    (by simp [mkCurve])

/-- A double cover of `ℙ¹` by a genus-2 curve with 6 simple ramification points. -/
def genus2CoverP1 : CurveCoverData :=
  CurveCoverData.mk' (mkCurve 2) (mkCurve 0) 2 6
    (by norm_num)
    (by norm_num)
    (by simp [mkCurve])

/-- A double cover of `ℙ¹` by a genus-3 curve with 8 simple ramification points. -/
def genus3CoverP1 : CurveCoverData :=
  CurveCoverData.mk' (mkCurve 3) (mkCurve 0) 2 8
    (by norm_num)
    (by norm_num)
    (by simp [mkCurve])

/-- Hyperelliptic cover: a generic double cover `X → ℙ¹` where `X` has genus `g`
and the cover has `2g + 2` simple ramification points. -/
def hyperellipticCover (g : ℕ) : CurveCoverData :=
  CurveCoverData.mk' (mkCurve g) (mkCurve 0) 2 (2 * (g : ℤ) + 2)
    (by linarith [Int.natCast_nonneg g])
    (by norm_num)
    (by simp [mkCurve]; linarith [Int.natCast_nonneg g])

end RiemannHurwitzDegree
end
