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
public import Instance.Patching_SystemTypes
public import Class.Patching_SystemTypes

@[expose] public section

set_option autoImplicit false

open IsLocalRing

open RingTheory in

noncomputable def Module.depth (R M : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] : ℕ∞ :=
  sSup { List.length s | (s : List R)
    (_ : Sequence.IsWeaklyRegular M s)
    (_ : ∀ r ∈ s, r ∈ maximalIdeal R) }
