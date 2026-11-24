module
public import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailRG
public import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockRGPackage

variable {n : ℕ} {α : Type}


noncomputable def certificate {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) : RGCertificate M :=
  P.hyperbolicSplitting.certificate scale M

end FinitePlusTailBlockRGPackage
end Exact3D
end StatMech
