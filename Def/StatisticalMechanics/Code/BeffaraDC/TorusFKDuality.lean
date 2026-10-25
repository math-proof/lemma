/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusGeometricEuler.Part3
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


def torusDualConfig (L : ℕ)
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    ConfigSpace (Sym2 (ZMod L × ZMod L)) :=
  fun e => !(ω (Sym2.map (torusQuarterTurn L) e))


def torusQuarterTurnEdge (L : ℕ) :
    Sym2 (ZMod L × ZMod L) ≃ Sym2 (ZMod L × ZMod L) where
  toFun := Sym2.map (torusQuarterTurn L)
  invFun := Sym2.map (torusQuarterTurn L).symm
  left_inv e := by
    calc
      _ = Sym2.map ((torusQuarterTurn L).symm ∘ torusQuarterTurn L) e := by
        exact (congrFun (Sym2.map_comp (g := (torusQuarterTurn L).symm)
          (f := torusQuarterTurn L)) e).symm
      _ = Sym2.map id e := by
        congr 2
        funext x
        exact (torusQuarterTurn L).symm_apply_apply x
      _ = e := congrFun Sym2.map_id e
  right_inv e := by
    calc
      _ = Sym2.map (torusQuarterTurn L ∘ (torusQuarterTurn L).symm) e := by
        exact (congrFun (Sym2.map_comp (g := torusQuarterTurn L)
          (f := (torusQuarterTurn L).symm)) e).symm
      _ = Sym2.map id e := by
        congr 2
        funext x
        exact (torusQuarterTurn L).apply_symm_apply x
      _ = e := congrFun Sym2.map_id e


end StatMech.BeffaraDC
