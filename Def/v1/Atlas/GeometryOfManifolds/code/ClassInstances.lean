/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ClassInstances.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.GeometryOfManifolds.code.PolynomialDFS.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.PolynomialDFS
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.TwoDimDFS
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AlmostComplexManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.MoserDarboux
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.FourManifoldsSW
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ArnoldConjecture
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.PontrjaginObstructions
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HodgeTheory
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ChernClassProperties
import Instance.v1.Atlas.GeometryOfManifolds.code.TrivialDFS
import Def.v1.Atlas.GeometryOfManifolds.code.TwoDimDFS.Part3
import Structure.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part4
import Structure.v1.Atlas.GeometryOfManifolds.code.MoserDarboux.Part2
import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part8
import Class.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture.Part4
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Class.v1.Atlas.GeometryOfManifolds.code.HardLefschetz
import Structure.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions.Part7
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
import Def.v1.Atlas.GeometryOfManifolds.code.ChernClassProperties.Part2
import Instance.v1.Atlas.GeometryOfManifolds.code.ClassInstances.Part2
set_option autoImplicit false
set_option maxHeartbeats 800000


/-- Trivial symplectic manifold structure on the singleton differential-form scaffolding. -/
noncomputable def trivialSymplecticManifold : SymplecticManifold TrivialΩ TrivialVF where
  ω := PUnit.unit
  closed := Subsingleton.elim _ _
  nondegenerate := by
    intro a b _
    exact Subsingleton.elim a b


/-- Trivial $\mathrm{Spin}^{\mathbb{C}}$ structure on $\mathbb{R}^4$ with spinor bundles
$S^\pm = \mathbb{C}$ and zero curvature data; provides a concrete witness for the abstract API. -/
noncomputable def trivialSpinC : SpinCStructure E4Model PUnit PUnit where
  SectionsPlus := ℂ
  SectionsMinus := ℂ
  instACGPlus := inferInstance
  instModPlus := inferInstance
  instACGMinus := inferInstance
  instModMinus := inferInstance
  nontrivial_plus := inferInstance
  c₁_L := 0
  Q_eval := fun _ => 0
  c₁_pair := fun _ => 0
  metric_pairing := fun _ _ => 0
  γ_plus_to_minus := fun _ _ => 0
  γ_minus_to_plus := fun _ _ => 0
  γ_on_2forms := fun _ x => x
  γ_on_2forms_minus := fun _ _ => 0
  hodge_star := id
  hodge_star_invol := fun _ => rfl
  hodge_clifford_plus := fun _ _ => rfl
  hodge_clifford_minus := by intros; simp
  gamma_anticomm := by intros; simp [mul_zero, zero_smul]
  hermitianInnerPlus := fun z w => (z * starRingEnd ℂ w).re
  normSqPlus := fun z => (z * starRingEnd ℂ z).re
  normSq_nonneg := fun z => by rw [Complex.mul_conj]; simp [Complex.normSq_nonneg]
  normSq_zero_iff := fun z => by
    constructor
    · intro h
      have h1 : (z * starRingEnd ℂ z).re = 0 := h
      rw [Complex.mul_conj] at h1
      have h2 : Complex.normSq z = 0 := by exact_mod_cast h1
      exact Complex.normSq_eq_zero.mp h2
    · intro h
      rw [h]
      simp
  hermitian_norm_compat := fun _ => rfl
  hermitian_smul_left := fun c z w => by
    show ((c • z) * starRingEnd ℂ w).re = c * (z * starRingEnd ℂ w).re
    rw [Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]

