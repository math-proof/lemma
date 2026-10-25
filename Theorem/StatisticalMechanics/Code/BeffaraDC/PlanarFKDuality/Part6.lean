/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
open Finset SimpleGraph Set


namespace StatMech

namespace BeffaraDC

open Lattice Ising Walls


theorem pfd_dualWeight_pos (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < pfdDualWeight P p q K := by
  unfold pfdDualWeight edgeProductCount
  have h1p : 0 < 1 - p := by linarith
  exact mul_pos (mul_pos (pow_pos hp _) (pow_pos h1p _)) (pow_pos hq _)

theorem pfd_dualZ_pos (P : PlanarZ2Subgraph) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < pfdDualZ P p q := by
  unfold pfdDualZ
  exact Finset.sum_pos
    (fun omega _ => pfd_dualWeight_pos P (FK.openSub P.G omega) hp hp1 hq)
    Finset.univ_nonempty


theorem pfd_partition_duality (P : PlanarZ2Subgraph) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkZ P.G p q * q ^ (P.G.edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V *
        pfdDualZ P (dualParam p q) q := by
  unfold FK.fkZ pfdDualZ
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omega _
  exact pfd_fkWeight_duality P omega hp hp1 hq


theorem pfd_fkProb_duality (P : PlanarZ2Subgraph)
    (omega : ConfigSpace (Sym2 P.V)) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkProb P.G p q omega = pfdDualProb P (dualParam p q) q omega := by
  have hps0 : 0 < dualParam p q := dualParam_pos hp hp1 hq
  have hps1 : dualParam p q < 1 := dualParam_lt_one hp hp1 hq
  have hZp : FK.fkZ P.G p q ≠ 0 := FK.fkZ_ne_zero P.G hp hp1 hq
  have hZd : pfdDualZ P (dualParam p q) q ≠ 0 :=
    (pfd_dualZ_pos P hps0 hps1 hq).ne'
  let A := q ^ (P.G.edgeFinset.card + 1)
  let B := (p / (1 - dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V
  let wp := FK.fkWeight P.G p q omega
  let wd := pfdDualWeight P (dualParam p q) q (FK.openSub P.G omega)
  have hA : 0 < A := pow_pos hq _
  have hB : 0 < B := by
    have hden : 0 < 1 - dualParam p q := by linarith
    exact mul_pos (pow_pos (div_pos hp hden) _) (pow_pos hq _)
  have hw : wp * A = B * wd := pfd_fkWeight_duality P omega hp hp1 hq
  have hZ : FK.fkZ P.G p q * A = B * pfdDualZ P (dualParam p q) q :=
    pfd_partition_duality P hp hp1 hq
  have hcross : wp * pfdDualZ P (dualParam p q) q = wd * FK.fkZ P.G p q := by
    apply mul_left_cancel₀ hB.ne'
    calc
      B * (wp * pfdDualZ P (dualParam p q) q) =
          wp * (B * pfdDualZ P (dualParam p q) q) := by ring
      _ = wp * (FK.fkZ P.G p q * A) := by rw [hZ]
      _ = (wp * A) * FK.fkZ P.G p q := by ring
      _ = (B * wd) * FK.fkZ P.G p q := by rw [hw]
      _ = B * (wd * FK.fkZ P.G p q) := by ring
  unfold FK.fkProb pfdDualProb
  apply (div_eq_div_iff hZp hZd).2
  simpa only [wp, wd] using hcross

end BeffaraDC
end StatMech
