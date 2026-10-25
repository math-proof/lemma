/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ConfigReachability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Structure.v1.Atlas.TheoryOfComputation.code.ConfigReachability
open SpaceComplexity


namespace ConfigReachability

variable {Q : Type} {Γ : Type}

/-- The configuration graph `G_{M,w}` of NTM `M` on input `w`: vertices are TM configurations
and edges are single steps `M.step`. -/
def mkConfigGraph (M : NTM Q Γ) (_w : List Γ) : ConfigGraph Q Γ where
  Vertex := TuringMachine.Config Q Γ
  Adj := M.step

/-- Reachability in a configuration graph: `Reachable c₁ c₂` is the reflexive–transitive closure
of the adjacency relation. -/
def ConfigGraph.Reachable (G : ConfigGraph Q Γ) (c₁ c₂ : G.Vertex) : Prop :=
  Relation.ReflTransGen G.Adj c₁ c₂

end ConfigReachability
