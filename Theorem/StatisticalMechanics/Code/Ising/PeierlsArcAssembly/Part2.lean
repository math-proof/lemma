/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InsideCoveringClose
import Theorem.StatisticalMechanics.Code.Ising.PeierlsPlanarAssembly
import Def.StatisticalMechanics.Code.Ising.PeierlsArcAssembly
open Set SimpleGraph Function


set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice


variable {W : Type*} {G : SimpleGraph W}


variable {V : Type*} [Finite V] [DecidableEq V]


theorem paa_two_components_of_arcNoSeparation (A : SimpleGraph V) (B' : Set (Sym2 V)) {a b : V}
    (h1 : paa_ArcNoSeparation A B')
    (he : s(a, b) ∈ (A.deleteEdges B').edgeSet)
    (h2 : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
    Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = 2 :=
  ecc_two_components_tree_plus_bridge A B' h1 he h2


theorem paa_bridge_of_separation (A : SimpleGraph V) (B' : Set (Sym2 V)) {a b : V}
    (hsep : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
    ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b :=
  hsep


theorem paa_dualModel_of_arcNoSeparation (A : SimpleGraph V) (B' : Set (Sym2 V)) {a b : V}
    (h1 : paa_ArcNoSeparation A B')
    (he : s(a, b) ∈ (A.deleteEdges B').edgeSet)
    (hsep : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
    ecc_DualCutModel A B' a b :=
  ⟨h1, he, hsep⟩


theorem paa_two_components_of_dualModel (A : SimpleGraph V) (B' : Set (Sym2 V)) {a b : V}
    (h1 : paa_ArcNoSeparation A B')
    (he : s(a, b) ∈ (A.deleteEdges B').edgeSet)
    (hsep : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
    Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = 2 :=
  ecc_two_components_of_dualModel A B' (paa_dualModel_of_arcNoSeparation A B' h1 he hsep)


end Ising
end StatMech
