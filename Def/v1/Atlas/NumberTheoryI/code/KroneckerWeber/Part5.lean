module
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Theorem.v1.Atlas.NumberTheoryI.code.GroupCounts.Part8
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.GroupCounts
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeberLocal2
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.ResidueFieldHelper
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.CyclotomicDVRInstances
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
public import Theorem.v1.Atlas.NumberTheoryI.code.KroneckerWeberLocal2.Part2
public import Theorem.v1.Atlas.NumberTheoryI.code.ResidueFieldHelper
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
public import Instance.v1.Atlas.NumberTheoryI.code.CyclotomicDVRInstances
public import Theorem.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open IsDedekindDomain in
def no_Z4Z_cube_extension := @KroneckerWeber.lemma_20_11_no_Z4Z3

def lemma_20_11 := @KroneckerWeber.lemma_20_11

def theorem_11_23_part1_separable := @KroneckerWeber.theorem_11_23_part1_separable

def theorem_11_23_part2_unique_prime := @KroneckerWeber.theorem_11_23_part2_unique_prime

def thm_11_23_part6_galois_implication := @KroneckerWeber.thm_11_23_part6_galois_implication

end
