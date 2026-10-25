/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailRG
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockRGPackage

variable {n : ℕ} {α : Type}


@[simp] theorem stableCertificate_map
    (P : FinitePlusTailBlockRGPackage n α) :
    P.stableCertificate.map = P.blockBounds.map :=
  rfl

@[simp] theorem stableCertificate_c
    (P : FinitePlusTailBlockRGPackage n α) :
    P.stableCertificate.c = P.c :=
  rfl

@[simp] theorem stableCertificate_finiteToFinite
    (P : FinitePlusTailBlockRGPackage n α) :
    P.stableCertificate.finiteToFinite = P.blockBounds.finiteToFinite :=
  rfl

@[simp] theorem stableCertificate_tailToFinite
    (P : FinitePlusTailBlockRGPackage n α) :
    P.stableCertificate.tailToFinite = P.blockBounds.tailToFinite :=
  rfl

@[simp] theorem stableCertificate_finiteToTail
    (P : FinitePlusTailBlockRGPackage n α) :
    P.stableCertificate.finiteToTail = P.blockBounds.finiteToTail :=
  rfl

@[simp] theorem stableCertificate_tailToTail
    (P : FinitePlusTailBlockRGPackage n α) :
    P.stableCertificate.tailToTail = P.blockBounds.tailToTail :=
  rfl


end FinitePlusTailBlockRGPackage
end Exact3D
end StatMech
