/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped LinearAlgebra.Projectivization
open ExteriorAlgebra

namespace GrassmannianProjective

/-- Any order embedding `Fin n ↪o Fin n` is the identity, since a strictly increasing bijection
on `Fin n` must be the identity. -/
lemma orderEmb_fin_eq_id (n : ℕ) (f : Fin n ↪o Fin n) (i : Fin n) : f i = i := by
  have hf := f.strictMono
  have h_surj : Function.Surjective f := Finite.surjective_of_injective f.injective
  have h_ge : ∀ j : Fin n, (j : ℕ) ≤ (f j : ℕ) := by
    intro ⟨j, hj⟩
    induction j with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hk : k < n := Nat.lt_of_succ_lt hj
      have hih := ih hk
      have hlt : (f ⟨k, hk⟩ : ℕ) < (f ⟨k + 1, hj⟩ : ℕ) :=
        hf (show (⟨k, hk⟩ : Fin n) < ⟨k + 1, hj⟩ by simp [Fin.lt_def])
      simp only at hih hlt ⊢; omega
  have h_le : ∀ j : Fin n, (f j : ℕ) ≤ (j : ℕ) := by
    by_contra h; push Not at h; obtain ⟨j, hj⟩ := h
    set e := Equiv.ofBijective f ⟨f.injective, h_surj⟩
    have hsum : ∑ i : Fin n, (f i : ℕ) = ∑ i : Fin n, (i : ℕ) := by
      conv_rhs => rw [show (fun i : Fin n => (i : ℕ)) =
        (fun i => (e (e.symm i) : ℕ)) from by ext; simp]
      rw [← Equiv.sum_comp e.symm]; simp [e, Equiv.ofBijective]
    exact absurd hsum (Nat.ne_of_gt
      (Finset.sum_lt_sum (fun i _ => h_ge i) ⟨j, Finset.mem_univ j, by omega⟩))
  exact Fin.ext (Nat.le_antisymm (h_le i) (h_ge i))

variable {K : Type*} [Field K]

/-- The exterior power of a basis is nonzero: `e_1 ∧ ... ∧ e_n ≠ 0`. -/
lemma ιMulti_basis_ne_zero {n : ℕ} {W : Type*} [AddCommGroup W] [Module K W]
    (b : Module.Basis (Fin n) K W) :
    (exteriorPower.ιMulti K n (fun i => b i)) ≠ 0 := by
  intro h
  set s : Set.powersetCard (Fin n) n := ⟨Finset.univ, Finset.card_fin n⟩
  have hdiag := exteriorPower.ιMultiDual_apply_diag K n b s
  have key : exteriorPower.ιMulti_family K n (⇑b) s =
      exteriorPower.ιMulti K n (fun i => b i) := by
    simp only [exteriorPower.ιMulti_family, exteriorPower.ιMulti]
    congr 1; funext i
    show b ((Set.powersetCard.ofFinEmbEquiv.symm s) i) = b i
    congr 1; exact orderEmb_fin_eq_id n (Set.powersetCard.ofFinEmbEquiv.symm s) i
  rw [key] at hdiag
  rw [show exteriorPower.ιMulti K n (fun i => b i) = (0 : ↥(⋀[K]^n W)) from
    Subtype.val_injective (by simp [h]), map_zero] at hdiag
  exact zero_ne_one hdiag

section GrassmannianDef

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]

/-- The Grassmannian `Gr(k, V)` as a set of `k`-dimensional subspaces of `V`. -/
def SubspaceGr (k : ℕ) := {W : Submodule K V // Module.finrank K W = k}

end GrassmannianDef

section PluckerEmbedding

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

/-- Choose a basis `Fin k → W` for a `k`-dimensional subspace `W` of `V`. -/
noncomputable def subspaceBasis (k : ℕ) (W : Submodule K V)
    (hk : Module.finrank K W = k) : Module.Basis (Fin k) K W :=
  (Module.finBasis K W).reindex (Fin.castOrderIso hk).toEquiv

/-- Plücker coordinate of `W`: the image of `e_1 ∧ ... ∧ e_k` in `⋀^k V` under the inclusion. -/
noncomputable def pluckerCoord (k : ℕ) (W : Submodule K V)
    (hk : Module.finrank K W = k) : ↥(⋀[K]^k V) :=
  let b := subspaceBasis K V k W hk
  exteriorPower.map k W.subtype (exteriorPower.ιMulti K k (fun i => b i))

omit [Module.Free K V] in
/-- The Plücker coordinate of a `k`-dimensional subspace is nonzero, so it defines a point in `P(⋀^k V)`. -/
theorem plucker_coord_ne_zero (k : ℕ) (W : Submodule K V)
    (hk : Module.finrank K W = k) :
    pluckerCoord K V k W hk ≠ 0 := by
  unfold pluckerCoord
  intro h

  obtain ⟨Q, hQ⟩ := W.exists_isCompl
  have hinj := exteriorPower.map_injective
    (Submodule.linearProjOfIsCompl W Q hQ)
    (Submodule.linearProjOfIsCompl_comp_subtype hQ) (n := k)

  have hne : (exteriorPower.ιMulti K k
      (fun i => (subspaceBasis K V k W hk) i)) ≠ 0 :=
    ιMulti_basis_ne_zero (subspaceBasis K V k W hk)
  exact hne (hinj (by rwa [map_zero]))

/-- Plücker map `Gr(k, V) → P(⋀^k V)` sending `W` to the projective class of `e_1 ∧ ... ∧ e_k`. -/
noncomputable def pluckerMap (k : ℕ) : SubspaceGr K V k → ℙ K (⋀[K]^k V) :=
  fun ⟨W, hk⟩ => Projectivization.mk K (pluckerCoord K V k W hk) (plucker_coord_ne_zero K V k W hk)

/-- A `k`-vector `ω ∈ ⋀^k V` is decomposable if it can be written as a wedge `v_1 ∧ ... ∧ v_k`. -/
def IsDecomposableExtPower (k : ℕ) (ω : ⋀[K]^k V) : Prop :=
  ∃ (v : Fin k → V), ω = exteriorPower.ιMulti K k v

/-- The locus of decomposable classes in `P(⋀^k V)`, i.e. the image of the Plücker map. -/
def DecomposableProjective (k : ℕ) : Set (ℙ K (⋀[K]^k V)) :=
  {p | ∃ (v : Fin k → V) (hv : exteriorPower.ιMulti K k v ≠ 0),
    p = Projectivization.mk K (exteriorPower.ιMulti K k v) hv}

/-- A subset of `P(⋀^k V)` is Zariski closed by quadratics if it is the zero locus of
homogeneous degree-2 polynomial functions (the Plücker relations). -/
def IsZariskiClosedByQuadratics (k : ℕ) (S : Set (ℙ K (⋀[K]^k V))) : Prop :=
  ∃ (ι : Type) (polys : ι → (⋀[K]^k V) → K),
    (∀ i, ∀ (c : K) (v : ⋀[K]^k V), polys i (c • v) = c ^ 2 * polys i v) ∧
    S = {p : ℙ K (⋀[K]^k V) | ∃ (v : ⋀[K]^k V) (hv : v ≠ 0),
      p = Projectivization.mk K v hv ∧ ∀ i, polys i v = 0}

/-- The image of the Plücker embedding is cut out by quadratic Plücker relations. -/
end PluckerEmbedding

section PluckerRelation

variable {K : Type*} [CommRing K] {M : Type*} [AddCommGroup M] [Module K M]

/-- A degree-2 element of the exterior algebra is decomposable if it equals a single wedge `v₁ ∧ v₂`. -/
def IsDecomposableDeg2 (ω : ExteriorAlgebra K M) : Prop :=
  ∃ v₁ v₂ : M, ω = ι K v₁ * ι K v₂
