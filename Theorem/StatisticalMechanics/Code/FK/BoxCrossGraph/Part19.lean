/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


theorem crossShiftAdd_pos {d n : ℕ} {p q : ℝ} (hp1 : p < 1) (hq : 0 < q)
    (D : SimpleGraph (boxVerts d (n+1))) : 0 < crossShiftAdd d n p q D :=
  mul_pos (pow_pos (by linarith) _) (pow_pos hq _)


theorem bcWeight_crossExt_add (d n : ℕ) {p q : ℝ} (ω : ConfigSpace (Sym2 (boxVerts d n)))
    {D : SimpleGraph (boxVerts d (n+1))} [DecidableRel D.Adj] (hD : IsAnnulusWiring d n D) :
    bcWeight (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) p q (crossExt d n ω)
      = wiredFkWeight (boxGraph d n) (boxBoundary d n) p q ω * crossShiftAdd d n p q D := by
  rw [bcWeight, numClustersBC_crossExt_add d n ω hD, edgeProduct_crossExt, wiredFkWeight,
    crossShiftAdd, pow_add]
  ring


theorem inducedBcZ_innerEdgeFinset_add (d n : ℕ) {p q : ℝ}
    {D : SimpleGraph (boxVerts d (n+1))} [DecidableRel D.Adj]
    (hD : IsAnnulusWiring d n D) :
    inducedBcZ (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) p q
        (innerEdgeFinset d n) (fun _ => false)
      = wiredFkZ (boxGraph d n) (boxBoundary d n) p q * crossShiftAdd d n p q D := by
  rw [inducedBcZ, condFibre_eq_image_crossExt,
    Finset.sum_image (fun a _ b _ h => by
      have := congrArg (innerRestrict d n) h
      rwa [innerRestrict_crossExt, innerRestrict_crossExt] at this),
    wiredFkZ, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ω _ => bcWeight_crossExt_add d n ω hD)


theorem condBcProb_crossExt_eq_wiredFkProb_add (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    {D : SimpleGraph (boxVerts d (n+1))} [DecidableRel D.Adj]
    (hD : IsAnnulusWiring d n D) :
    condBcProb (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) p q
        (innerEdgeFinset d n) (fun _ => false) (crossExt d n ω)
      = wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  rw [condBcProb, if_pos (agreesOff_crossExt d n ω), bcWeight_crossExt_add d n ω hD,
    inducedBcZ_innerEdgeFinset_add d n hD, wiredFkProb,
    mul_div_mul_right _ _ (crossShiftAdd_pos hp1 hq D).ne']

end FK
end StatMech
