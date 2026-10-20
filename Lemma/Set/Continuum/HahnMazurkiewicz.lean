import Mathlib
import sympy.Basic
import sympy.atlas.Topology.Continuum.HahnMazurkiewicz
open Topology
open Filter
open MathlibExt.Topology.Continuum.HahnMazurkiewiczWanted


/--
[hahnMazurkiewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Continuum/HahnMazurkiewicz.lean)
-/
@[path]
private lemma hahnMazurkiewicz_eq
  [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X] [LocallyConnectedSpace X] [T2Space X] [SecondCountableTopology X] [Nonempty X] :
-- imply
  ∃ (f : unitInterval → X), Continuous f ∧ Function.Surjective f := by
-- proof
  apply MathlibExt.Topology.Continuum.HahnMazurkiewiczWanted.hahnMazurkiewicz


-- created on 2026-10-20
