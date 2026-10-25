/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Structure.StatisticalMechanics.Code.Exact3D.StableKeyCertificate


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyRecord

def toKey {maxDegree maxRange : ℕ} (r : StableKeyRecord)
    (hdegree : r.degree ≤ maxDegree) (hrange : r.range ≤ maxRange) :
    StableKey maxDegree maxRange :=
  toLex (r.support,
    toLex (⟨r.degree, Nat.lt_succ_of_le hdegree⟩,
      ⟨r.range, Nat.lt_succ_of_le hrange⟩))


def ofKey {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) : StableKeyRecord :=
  let p := ofLex k
  let q := ofLex p.2
  { support := p.1
    degree := q.1.1
    range := q.2.1 }

end StableKeyRecord
end BoundedPolymerCase
end Exact3D
end StatMech
