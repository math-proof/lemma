/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardAtlas
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u


namespace CriticalIsoradialClosedFlatSurfaceEmbedding

theorem surface_kacWard_arf_formula
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {DualVertex Q Qstar : Type u}
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    (embedding : CriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Q Qstar)
    (weight : Sym2 V -> Real) :
    (forall lambda : SurfaceSpinStructure g,
      (1 - surfaceTwistedKacWardMatrix G embedding.atlas.phase
          embedding.atlas.edgeClass lambda
          (fun edge => (weight edge : Complex))).det =
        (surfaceTwistedSectorSquare
          (surfaceGraphSectorWeight G embedding.atlas.edgeClass weight)
          lambda : Complex)) /\
    surfaceUnsignedSectorSum
        (surfaceGraphSectorWeight G embedding.atlas.edgeClass weight) =
      ((2 : Real) ^ g)⁻¹ *
        ∑ lambda : SurfaceSpinStructure g,
          surfaceParitySign (surfaceArfParity lambda) *
            surfaceTwistedSectorRoot
              (surfaceGraphSectorWeight G embedding.atlas.edgeClass weight)
              lambda :=
  closedFlatSurfaceAtlas_kacWard_arf_formula G embedding.atlas
    embedding.admissibleConeAngles weight


theorem normalized_kacWard_duality
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {DualVertex Q Qstar : Type u}
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    (embedding : CriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Q Qstar) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - embedding.theta edge) *
        (1 - embedding.dualKacWard).det =
      kwIsoradialDualityNormalization V embedding.theta *
        (1 - embedding.primalKacWard).det :=
  embedding.toDualityCertificate.normalized_det_eq
    embedding.atlas.cellular.ribbonSystem
    embedding.atlas.cellular.cellularDualData embedding.character
    embedding.theta embedding.primalExceptional embedding.dualExceptional
    embedding.primalKacWard embedding.dualKacWard

end CriticalIsoradialClosedFlatSurfaceEmbedding
end StatMech.FrontierA
