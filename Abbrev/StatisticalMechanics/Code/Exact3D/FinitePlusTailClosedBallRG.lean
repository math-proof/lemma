module
public import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type}


abbrev hamiltonian (_C : FinitePlusTailClosedBallContractionCertificate n α) :
    EffectiveHamiltonian where
  carrier := FinitePlusTailState n α


end FinitePlusTailClosedBallContractionCertificate
end Exact3D
end StatMech
