/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonEmbedding.Part5
import Instance.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonParity


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectRibbonIndexSucc {n : ℕ} (hn : 0 < n)
    (z : Fin n × Fin 8) : Fin n × Fin 8 :=
  letI : NeZero n := ⟨hn.ne'⟩
  (if z.2 = Fin.last 7 then z.1 + 1 else z.1, z.2 + 1)

def fkRectBlackOrbitMedialRibbonIndexedDirection
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z : Fin (fkRectBlackOrbitList
        (fkRectConfigurationToMedialPairing R omega) d).length × Fin 8) :
    Fin 4 :=
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  fkRectMedialRibbonBlockDirection
    (pairing (l.get z.1).1.1) (l.get z.1).1.2 z.2

def fkRectRibbonRectStep (width height : ℕ) (mu : Fin 4)
    (p : ZMod width × ZMod height) : ZMod width × ZMod height :=
  match mu with
  | 0 => (p.1 + 1, p.2)
  | 1 => (p.1, p.2 + 1)
  | 2 => (p.1 - 1, p.2)
  | 3 => (p.1, p.2 - 1)

end
end StatMech.FrontierD
