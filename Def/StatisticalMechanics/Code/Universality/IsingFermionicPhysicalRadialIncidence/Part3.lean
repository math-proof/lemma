/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBond.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

noncomputable def fkIsingSquareInteriorRadialEndpoint
    (n : Nat) (hn : 0 < n) :
    FKIsingSquareInteriorRadialIncidence n hn → (fkSquareBoxPlanar n).V :=
  Quot.lift (fun d : FKIsingSquareInteriorRadialDart n =>
      fkIsingSquareDartEndpoint n d.1)
    (fun _ _ hxy => eq_of_sameCycle_of_step
      (fkIsingSquareInteriorRadialBondPerm n hn)
      (fun d : FKIsingSquareInteriorRadialDart n =>
        fkIsingSquareDartEndpoint n d.1)
      (fkIsingSquareInteriorRadial_endpoint_bondMate n hn) hxy)


noncomputable def fkIsingSquareInteriorRadialFaceKey
    (n : Nat) (hn : 0 < n) :
    FKIsingSquareInteriorRadialIncidence n hn → Int × Int :=
  Quot.lift (fun d : FKIsingSquareInteriorRadialDart n =>
      fkIsingSquareWedgeFaceKey n d.1)
    (fun _ _ hxy => eq_of_sameCycle_of_step
      (fkIsingSquareInteriorRadialBondPerm n hn)
      (fun d : FKIsingSquareInteriorRadialDart n =>
        fkIsingSquareWedgeFaceKey n d.1)
      (fkIsingSquareInteriorRadial_faceKey_bondMate n hn) hxy)


noncomputable def fkIsingSquareInteriorRadialIncrement
    (n : Nat) (hn : 0 < n) :
    FKIsingSquareInteriorRadialIncidence n hn → Real :=
  Quot.lift (fun d : FKIsingSquareInteriorRadialDart n =>
      fkIsingSquareWiredPrimitiveIncrement n hn (.dart d.1))
    (fun _ _ hxy => eq_of_sameCycle_of_step
      (fkIsingSquareInteriorRadialBondPerm n hn)
      (fun d : FKIsingSquareInteriorRadialDart n =>
        fkIsingSquareWiredPrimitiveIncrement n hn (.dart d.1))
      (fkIsingSquareInteriorRadial_increment_bondMate n hn) hxy)

end
end StatMech.Universality
