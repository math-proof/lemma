/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Instance.StatisticalMechanics.Code.IsingFK.Coloring
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem compatible_iff_constOnOpen {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    Compatible G σ ω ↔ ConstOnOpen G ω σ :=
  ⟨fun h x y hadj => h x y hadj.1 hadj.2, fun h x y h1 h2 => h x y ⟨h1, h2⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem compatible_constant_on_cluster {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V))
    (h : Compatible G σ ω) {x y : V} (r : (openSub G ω).Reachable x y) : σ x = σ y :=
  constOnOpen_reachable G ω σ ((compatible_iff_constOnOpen G σ ω).1 h) r


end IsingFK
end StatMech
