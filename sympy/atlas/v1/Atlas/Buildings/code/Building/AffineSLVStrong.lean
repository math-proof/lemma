/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.AffineSLV
import Lemma.Set.IsHomothetic_πLattice
import Lemma.Set.ConjSet.eq.Image
import sympy.atlas.v1.Atlas.Buildings.code.Building.GroupApplicationsCh17
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Topology.Algebra.Group.Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AffineBuildingSLVStrong

open AffineBuildingSLV AffineBuildingSLVAxioms


/-- Topological hypotheses on the fraction field $k$ of a complete DVR: the valuation
ring $\mathfrak{o}$ is open and compact in $k$, its maximal ideal is open, $k$ is a
$T_1$ topological ring. This is the package of assumptions needed to make the
Iwahori subgroup compact-open in $SL_V(k)$. -/
class DVRTopologicalAssumptions (C : DVRContext) [TopologicalSpace C.k] : Prop where
  isOpen_valRing : IsOpen {x : C.k | C.isInO x}
  isOpen_maxIdeal : IsOpen {x : C.k | C.isInMaxIdeal x}
  isTopologicalRing : IsTopologicalRing C.k
  isCompact_valRing : IsCompact {x : C.k | C.isInO x}
  t1Space : T1Space C.k


/-- The $j$-th standard basis vector $e_j \in k^n$. -/
noncomputable def stdBasisVec (C : DVRContext) (j : Fin C.n) : Fin C.n → C.k :=
  fun i => if i = j then 1 else 0

/-- Each standard basis vector $e_j$ is nonzero. -/
theorem stdBasisVec_ne_zero (C : DVRContext) (j : Fin C.n) : stdBasisVec C j ≠ 0 := by
  intro h
  have : stdBasisVec C j j = (0 : Fin C.n → C.k) j := by rw [h]
  simp [stdBasisVec] at this

/-- The $j$-th coordinate line $k \cdot e_j$ in $k^n$, packaged as a Line. -/
noncomputable def stdLine (C : DVRContext) (j : Fin C.n) : Line C :=
  ⟨stdBasisVec C j, stdBasisVec_ne_zero C j⟩

/-- Pointwise evaluation: $(\sum_j c_j e_j)(i) = c_i$. -/
theorem sum_std_basis_apply (C : DVRContext) (coeffs : Fin C.n → C.k) (i : Fin C.n) :
    (∑ j, coeffs j * stdBasisVec C j i) = coeffs i := by
  rw [Finset.sum_eq_single i]
  · simp [stdBasisVec]
  · intro j _ hji
    simp [stdBasisVec, Ne.symm hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Functional form: $\sum_j c_j e_j = c$ as vectors in $k^n$. -/
theorem sum_std_basis_eq (C : DVRContext) (coeffs : Fin C.n → C.k) :
    (fun i => ∑ j, coeffs j * stdBasisVec C j i) = coeffs := by
  funext i
  exact sum_std_basis_apply C coeffs i

/-- The standard frame in $k^n$ consisting of the coordinate lines $k \cdot e_j$. -/
noncomputable def stdFrame (C : DVRContext) : Frame C where
  lines := stdLine C
  spans := by
    intro v
    exact ⟨v, (sum_std_basis_eq C v).symm⟩
  independent := by
    intro coeffs h j
    have hj : (fun i => ∑ k_1, coeffs k_1 * (stdLine C k_1).generator i) j
              = (0 : Fin C.n → C.k) j := congr_fun h j
    simp only [stdLine, Pi.zero_apply] at hj
    rw [sum_std_basis_apply] at hj
    exact hj


/-- The special linear group $SL_n(k) = SL_V(k)$ acting on the affine building of
type $\tilde A_{n-1}$. -/
abbrev SLV (C : DVRContext) := Matrix.SpecialLinearGroup (Fin C.n) C.k


/-- The $(i,j)$-th matrix entry of an element of $SL_n(k)$, as a function $SL_n(k)
\to k$. -/
def matEntryProj (C : DVRContext) (i j : Fin C.n) : SLV C → C.k :=
  fun g => (g : Matrix (Fin C.n) (Fin C.n) C.k) i j

/-- The Iwahori condition on the $(i,j)$-entry: lies in the maximal ideal
$\mathfrak{m}$ if $i > j$ (strictly below the diagonal) and in $\mathfrak{o}$
otherwise. -/
def iwahoriEntryCondition (C : DVRContext) (i j : Fin C.n) : Set C.k :=
  if i.val > j.val then {x | C.isInMaxIdeal x} else {x | C.isInO x}

/-- The Iwahori subset of $SL_n(k)$: matrices in $SL_n(\mathfrak{o})$ whose
reduction modulo $\mathfrak{m}$ is upper-triangular. -/
def IwahoriSetSLV (C : DVRContext) : Set (SLV C) :=
  ⋂ (i : Fin C.n), ⋂ (j : Fin C.n),
    matEntryProj C i j ⁻¹' iwahoriEntryCondition C i j


/-- Axiomatic action of $SL_V(k)$ on the Bruhat-Tits building of $SL_V$: a
simplicial action together with the induced action on apartments and frames, and
sufficient hypotheses to run strong-transitivity arguments (preservation of
maximal simplices, frame/apartment compatibility, building chain data and
within-apartment chamber transitivity). -/
structure SLVAction (C : DVRContext) where
  act_simplex : SLV C → Simplex C → Simplex C
  act_mul : ∀ (g₁ g₂ : SLV C) (σ : Simplex C),
    act_simplex (g₁ * g₂) σ = act_simplex g₁ (act_simplex g₂ σ)
  act_one : ∀ (σ : Simplex C), act_simplex 1 σ = σ
  act_apartment : SLV C → Set (Simplex C) → Set (Simplex C)
  act_apartment_eq : ∀ (g : SLV C) (A : Set (Simplex C)),
    act_apartment g A = (act_simplex g) '' A
  act_preserves_maximal : ∀ (g : SLV C) (σ : Simplex C),
    σ.IsMaximal C → (act_simplex g σ).IsMaximal C
  act_frame : SLV C → Frame C → Frame C
  act_apartment_frame_compat : ∀ (g : SLV C) (F : Frame C),
    act_apartment g (Apartment C F) = Apartment C (act_frame g F)
  act_apartment_surj : ∀ (max_apts : Set (Set (Simplex C))),
    (∀ F : Frame C, Apartment C F ∈ max_apts) →
    ∀ (A' A₀ : Set (Simplex C)), A' ∈ max_apts → A₀ ∈ max_apts →
    ∀ g : SLV C, (∀ x ∈ A', act_simplex g x ∈ A₀) →
    (fun x => act_simplex g x) '' A' = A₀
  act_building_chain_data :
    ∀ (max_apts : Set (Set (Simplex C))),
    (∀ F : Frame C, Apartment C F ∈ max_apts) →
    ∀ (B : Subgroup (SLV C)) (A₀ : Set (Simplex C)),
    A₀ ∈ max_apts →
    ∀ (C₀ : Set (Simplex C)),
    C₀ ⊆ A₀ →
    (B : Set (SLV C)) = pointwiseFixer act_simplex C₀ →
    ∀ (A' : Set (Simplex C)), A' ∈ max_apts →
      C₀ ⊆ A' ∧
      ∃ (enum : ℕ → Simplex C),
        (∀ σ ∈ A', ∃ n, enum n = σ) ∧
        (∀ n, enum n ∈ A') ∧
        ∀ (Y : Set (Simplex C)), C₀ ⊆ Y → Y ⊆ A' →
          ∃ (A_i : Set (Simplex C)) (b_i : SLV C),
            Y ⊆ A_i ∧ b_i ∈ B ∧
            (∀ x ∈ A_i, act_simplex b_i x ∈ A₀)
  act_frame_chamber_trans :
    ∀ (F : Frame C) (C₁ C₂ : Simplex C),
      C₁.IsMaximal C → C₂.IsMaximal C →
      C₁ ∈ Apartment C F → C₂ ∈ Apartment C F →
      ∃ g : SLV C, act_simplex g C₁ = C₂ ∧
        act_apartment g (Apartment C F) = Apartment C F


/-- An $SL_V$-action on the building is strongly transitive with respect to an
apartment system $\mathcal A$ if for any two flagged pairs $(C_1, A_1)$ and
$(C_2, A_2)$ (maximal simplex in an apartment) some $g$ carries the first to the
second. -/
def IsStronglyTransitive (C : DVRContext) (α : SLVAction C)
    (𝒜 : Set (Set (Simplex C))) : Prop :=
  ∀ (C₁ : Simplex C) (A₁ : Set (Simplex C))
    (C₂ : Simplex C) (A₂ : Set (Simplex C)),
    C₁.IsMaximal C → C₂.IsMaximal C →
    A₁ ∈ 𝒜 → A₂ ∈ 𝒜 →
    C₁ ∈ A₁ → C₂ ∈ A₂ →
    ∃ g : SLV C, α.act_simplex g C₁ = C₂ ∧ α.act_apartment g A₁ = A₂

/-- The image of the valuation ring embedding $\mathfrak{o} \hookrightarrow k$ as a
subring of $k$. -/
noncomputable def imageSubring (C : DVRContext) : Subring C.k :=
  C.embed.range

/-- The canonical apartment system: apartments $A_F$ indexed by frames $F$ of $V$.
This is the maximal apartment system for the Bruhat-Tits building of $SL_V$. -/
def frameApartmentSystem (C : DVRContext) : Set (Set (Simplex C)) :=
  {A | ∃ F : Frame C, A = Apartment C F}

/-- A family of apartments is an apartment system if every member arises from a
frame and any two simplices lie together in some apartment of the system. -/
def IsApartmentSystem (C : DVRContext) (sys : Set (Set (Simplex C))) : Prop :=

  (∀ A ∈ sys, ∃ F : Frame C, A = Apartment C F) ∧

  (∀ σ₁ σ₂ : Simplex C, ∃ A ∈ sys, σ₁ ∈ A ∧ σ₂ ∈ A) ∧


  True

/-- An apartment system is maximal if it is an apartment system and contains every
other apartment system. -/
def IsMaximalApartmentSystem (C : DVRContext) (max_apts : Set (Set (Simplex C))) : Prop :=
  IsApartmentSystem C max_apts ∧
  (∀ sys : Set (Set (Simplex C)), IsApartmentSystem C sys → sys ⊆ max_apts)
