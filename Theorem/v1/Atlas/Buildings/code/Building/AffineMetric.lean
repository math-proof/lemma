/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
import Def.v1.Atlas.Buildings.code.AffineCoxeter.CanonicalMetric.Part2
import Lemma.Real.IsWInvariantEuclideanDist
import Mathlib.Topology.MetricSpace.Basic
import Def.v1.Atlas.Buildings.code.Building.AffineMetric.Part3
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Classical
open ChamberComplex
open AffineCoxeter


/-- A "cross" version of well-definedness: $x$ lies in a shared face
$\sigma$ and $y$ lies in a shared chamber $C$; the two apartments share
both $\sigma$ and $C$, so an isomorphism fixes both $x$ and $y$ and the
apartment distances agree. -/
theorem buildingDist_wellDefined_from_face_and_chamber_cross
    (b : Building V) (md : ApartmentMetricData b)
    (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
    (σ : Finset V) (C : Finset V)
    (hσ_A₁ : σ ∈ A₁.val.faces) (hσ_A₂ : σ ∈ A₂.val.faces)
    (hC_max : A₁.val.IsMaximal C) (hC_A₂ : C ∈ A₂.val.faces)
    (x y : V) (hx_σ : x ∈ σ) (hy_C : y ∈ C) :
    md.dist_fn A₁ x y = md.dist_fn A₂ x y := by

  obtain ⟨φ, hφ_σ, hφ_C⟩ :=
    b.apartmentSystem.iso_exists A₁.val A₁.property A₂.val A₂.property
      σ hσ_A₁ hσ_A₂ C hC_max hC_A₂

  have hφx : φ.toFun x = x := hφ_σ x hx_σ
  have hφy : φ.toFun y = y := hφ_C y hy_C

  have h_iso := md.iso_isometry A₁ A₂ φ φ.map_face x y
  rw [h_iso, hφx, hφy]

/-- Well-definedness without assuming a common face: if vertices
$\{v\}, \{w\}$ are both vertices of two apartments $A_1, A_2$ (no shared
edge required), then $\mathrm{dist}_{A_1}(v, w) = \mathrm{dist}_{A_2}(v, w)$.
The proof combines $v$ and $w$ across a third apartment via the
"cross" lemma in both directions. -/
theorem buildingDist_well_defined_clean (b : Building V) (md : ApartmentMetricData b)
    (v w : V)
    (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
    (hv₁ : {v} ∈ A₁.val.faces) (hw₁ : {w} ∈ A₁.val.faces)
    (hv₂ : {v} ∈ A₂.val.faces) (hw₂ : {w} ∈ A₂.val.faces) :
    md.dist_fn A₁ v w = md.dist_fn A₂ v w := by

  obtain ⟨_, _, cc₁, hcc₁_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A₁.val A₁.property
  have hw_cc₁ : {w} ∈ cc₁.toSimplicialComplex.faces := hcc₁_eq ▸ hw₁
  obtain ⟨C_w, hCw_max_cc, hw_sub_Cw⟩ := cc₁.exists_maximal {w} hw_cc₁
  have hCw_max : A₁.val.IsMaximal C_w := hcc₁_eq ▸ hCw_max_cc
  have hCw_bmax := b.apartmentSystem.maximal_in_apt_is_maximal A₁.val A₁.property C_w hCw_max

  obtain ⟨_, _, cc₂, hcc₂_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A₂.val A₂.property
  have hv_cc₂ : {v} ∈ cc₂.toSimplicialComplex.faces := hcc₂_eq ▸ hv₂
  obtain ⟨D_v, hDv_max_cc, hv_sub_Dv⟩ := cc₂.exists_maximal {v} hv_cc₂
  have hDv_max : A₂.val.IsMaximal D_v := hcc₂_eq ▸ hDv_max_cc
  have hDv_bmax := b.apartmentSystem.maximal_in_apt_is_maximal A₂.val A₂.property D_v hDv_max

  obtain ⟨A₃_val, hA₃_mem, hCw_A₃, hDv_A₃⟩ :=
    b.apartmentSystem.contains_pair C_w D_v hCw_bmax hDv_bmax
  let A₃ : { A // A ∈ b.apartmentSystem.apartments } := ⟨A₃_val, hA₃_mem⟩

  have hv_A₃ : {v} ∈ A₃.val.faces :=
    A₃_val.down_closed hDv_A₃ hv_sub_Dv (Finset.singleton_nonempty v)
  have hw_A₃ : {w} ∈ A₃.val.faces :=
    A₃_val.down_closed hCw_A₃ hw_sub_Cw (Finset.singleton_nonempty w)

  have hw_in_Cw : w ∈ C_w := Finset.singleton_subset_iff.mp hw_sub_Cw
  have h₁ := buildingDist_wellDefined_from_face_and_chamber_cross b md A₁ A₃
    {v} C_w hv₁ hv_A₃ hCw_max hCw_A₃ v w
    (Finset.mem_singleton.mpr rfl) hw_in_Cw

  have hv_in_Dv : v ∈ D_v := Finset.singleton_subset_iff.mp hv_sub_Dv
  have h₂_swap := buildingDist_wellDefined_from_face_and_chamber_cross b md A₂ A₃
    {w} D_v hw₂ hw_A₃ hDv_max hDv_A₃ w v
    (Finset.mem_singleton.mpr rfl) hv_in_Dv

  have h₂ : md.dist_fn A₂ v w = md.dist_fn A₃ v w := by
    rw [md.dist_symm A₂ v w, h₂_swap, md.dist_symm A₃ w v]

  rw [h₁, ← h₂]

