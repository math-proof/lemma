/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCanonicalDenseIncidence.Part6
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

theorem fkIsingExpandingSquareScale_mul_floor_succ_tendsto (c : Real) :
    Tendsto
      (fun k ↦ fkIsingExpandingSquareScale k *
        ((⌊c * (k + 1 : Real)⌋ : Int) : Real))
      atTop (nhds c) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hscale := (Metric.tendsto_nhds.1
    fkIsingExpandingSquareScale_tendsto_zero) epsilon hepsilon
  filter_upwards [hscale] with k hk
  rw [Real.dist_eq]
  have hspos : 0 < fkIsingExpandingSquareScale k :=
    fkIsingExpandingSquareScale_pos k
  have hscaleSucc :
      fkIsingExpandingSquareScale k * (k + 1 : Real) = 1 := by
    simp only [fkIsingExpandingSquareScale, one_div]
    push_cast
    exact inv_mul_cancel₀ (show (k : Real) + 1 ≠ 0 by positivity)
  have hupper :
      fkIsingExpandingSquareScale k *
          ((⌊c * (k + 1 : Real)⌋ : Int) : Real) ≤ c := by
    have hfloor := Int.floor_le (c * (k + 1 : Real))
    have hmul := mul_le_mul_of_nonneg_left hfloor hspos.le
    calc
      fkIsingExpandingSquareScale k *
          ((⌊c * (k + 1 : Real)⌋ : Int) : Real) ≤
          fkIsingExpandingSquareScale k * (c * (k + 1 : Real)) := hmul
      _ = c * (fkIsingExpandingSquareScale k * (k + 1 : Real)) := by ring
      _ = c := by rw [hscaleSucc, mul_one]
  have hlower :
      c - fkIsingExpandingSquareScale k <
        fkIsingExpandingSquareScale k *
          ((⌊c * (k + 1 : Real)⌋ : Int) : Real) := by
    have hfloor := Int.sub_one_lt_floor (c * (k + 1 : Real))
    have hmul := mul_lt_mul_of_pos_left hfloor hspos
    calc
      c - fkIsingExpandingSquareScale k =
          fkIsingExpandingSquareScale k *
            (c * (k + 1 : Real) - 1) := by
              rw [mul_sub, mul_one]
              calc
                c - fkIsingExpandingSquareScale k =
                    c * (fkIsingExpandingSquareScale k * (k + 1 : Real)) -
                      fkIsingExpandingSquareScale k := by rw [hscaleSucc, mul_one]
                _ = fkIsingExpandingSquareScale k * (c * (k + 1 : Real)) -
                      fkIsingExpandingSquareScale k := by ring
      _ < fkIsingExpandingSquareScale k *
          ((⌊c * (k + 1 : Real)⌋ : Int) : Real) := hmul
  have hnonpos :
      fkIsingExpandingSquareScale k *
          ((⌊c * (k + 1 : Real)⌋ : Int) : Real) - c ≤ 0 := by
    linarith
  rw [abs_of_nonpos hnonpos]
  have hk' : fkIsingExpandingSquareScale k < epsilon := by
    simpa [Real.dist_eq, abs_of_pos hspos] using hk
  linarith


theorem fkIsingDenseRationalIncidence_embedding_tendsto (q : Rat × Rat) :
    Tendsto
      (fun k ↦
        FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding
          (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k)
          (fkIsingSquareInteriorRadialEndpoint
            (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
            (fkIsingDenseRationalIncidence q k)))
      atTop (nhds (fkIsingRationalComplex q)) := by
  let cx : Real := ((q.1 : Real) + (q.2 : Real)) / 2
  let cy : Real := ((q.1 : Real) - (q.2 : Real)) / 2
  let x : Nat → Int := fun k ↦ ⌊cx * (k + 1 : Real)⌋
  let y : Nat → Int := fun k ↦ ⌊cy * (k + 1 : Real)⌋
  have hx : Tendsto
      (fun k ↦ fkIsingExpandingSquareScale k * ((x k : Int) : Real))
      atTop (nhds cx) := by
    simpa [x] using fkIsingExpandingSquareScale_mul_floor_succ_tendsto cx
  have hy : Tendsto
      (fun k ↦ fkIsingExpandingSquareScale k * ((y k : Int) : Real))
      atTop (nhds cy) := by
    simpa [y] using fkIsingExpandingSquareScale_mul_floor_succ_tendsto cy
  have hre := hx.add hy
  have him := hx.sub hy
  have hreComplex := (Complex.continuous_ofReal.tendsto (cx + cy)).comp hre
  have himComplex := (Complex.continuous_ofReal.tendsto (cx - cy)).comp him
  have hformula := hreComplex.add (himComplex.mul_const Complex.I)
  have htarget :
      ((cx + cy : Real) : Complex) +
          ((cx - cy : Real) : Complex) * Complex.I =
        fkIsingRationalComplex q := by
    simp [fkIsingRationalComplex, cx, cy]
    ring
  have hformula' : Tendsto
      (fun k ↦
        ((fkIsingExpandingSquareScale k * ((x k : Int) : Real) +
            fkIsingExpandingSquareScale k * ((y k : Int) : Real) : Real) :
          Complex) +
        ((fkIsingExpandingSquareScale k * ((x k : Int) : Real) -
            fkIsingExpandingSquareScale k * ((y k : Int) : Real) : Real) :
          Complex) * Complex.I)
      atTop (nhds (fkIsingRationalComplex q)) := by
    rw [← htarget]
    simpa only [Function.comp_apply] using hformula
  apply hformula'.congr'
  filter_upwards [fkIsingDenseRationalPrimal_eventually_interior q]
    with k hk
  have hxDef : x k = fkIsingDenseRationalPrimalX q k := by
    rfl
  have hyDef : y k = fkIsingDenseRationalPrimalY q k := by
    rfl
  rw [show fkIsingDenseRationalIncidence q k =
      fkIsingSquareInteriorRadialIncidenceOfInt
        (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
        (x k) (y k) (by simpa [hxDef, hyDef] using hk) by
    simp [fkIsingDenseRationalIncidence, hxDef, hyDef, hk]]
  rw [fkIsingSquareInteriorRadialIncidenceOfInt_endpoint]
  rw [fullSquareScaledVertexEmbedding_fullVertexOfInt]
  simp [Complex.ext_iff]
  constructor <;> ring


end
end StatMech.Universality
