-- Carved from Lemma/Definitions/Def_Patching_SystemTypes.lean: instance decls only.

module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Mathlib.Data.ENat.Lattice
public import Class.Patching_SystemTypes

@[expose] public section

set_option autoImplicit false

open IsLocalRing


instance (priority := 100) {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    [TopologicalSpace S] [IsTopologicalRing S] [Algebra.FiniteType R S] :
    Algebra.TopologicallyFG R S where
  out := have ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S); ⟨s, by simp [hs]⟩

