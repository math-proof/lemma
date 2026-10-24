/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CheckLebowitzPfisterReplicaOrbitAtoms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAtoms

#print axioms StatMech.Ising.lpReplicaOrbitConfigurationWeight_eq_multiplicity_mul_base
#print axioms StatMech.Ising.card_lpReplicaOrbitAtom
#print axioms StatMech.Ising.lpReplicaProfileOrbitMass_eq_card_atoms_mul_base
#print axioms StatMech.Ising.lpReplicaProfileOrbitBaseWeight_nonneg
#print axioms StatMech.Ising.lpReplicaProfileOrbitMass_le_add_of_card_atoms
#print axioms StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_of_atomCard
