/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean -/

import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import sympy.atlas.GroupTheory.BurnsidePaqb.ClassSum
import Lemma.Nat.ConjClass.of.IsConj
/-!
Central-character stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/CentralChar.lean`.
-/

namespace BurnsidePaqb

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
/-- A central group-algebra element acts on an irreducible representation by a
scalar (Schur's lemma via `asAlgebraHom`). -/
theorem exists_scalar_of_central {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ]
    (z : MonoidAlgebra ℂ G) (hz : ∀ w, w * z = z * w) :
    ∃ c : ℂ, ∀ v : V, ρ.asAlgebraHom z v = c • v := by
  classical
  let L : Module.End (MonoidAlgebra ℂ G) ρ.asModule :=
    { toFun := fun v => z • v
      map_add' := fun x y => smul_add z x y
      map_smul' := fun r x => by
        change z • (r • x) = r • (z • x)
        rw [← smul_assoc, ← smul_assoc]
        change (z * r) • x = (r * z) • x
        rw [(hz r).symm] }
  obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ).2 L
  refine ⟨c, fun v => ?_⟩
  have h1 : (algebraMap ℂ (Module.End (MonoidAlgebra ℂ G) ρ.asModule) c)
      (ρ.asModuleEquiv.symm v) = L (ρ.asModuleEquiv.symm v) := by rw [hc]
  have h2 : ∀ x : ρ.asModule,
      (algebraMap ℂ (Module.End (MonoidAlgebra ℂ G) ρ.asModule) c) x = c • x := by
    intro x
    simp [Algebra.algebraMap_eq_smul_one]
  have hL : ∀ x : ρ.asModule, L x = z • x := fun x => rfl
  rw [h2, hL] at h1
  have h4 : ρ.asModuleEquiv (c • ρ.asModuleEquiv.symm v) =
      ρ.asModuleEquiv (z • ρ.asModuleEquiv.symm v) := congrArg _ h1
  rw [map_smul, LinearEquiv.apply_symm_apply, ρ.asModuleEquiv_map_smul,
    LinearEquiv.apply_symm_apply] at h4
  exact h4.symm

section CentralScalar

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]

open Classical in
/-- Central character scalar: the scalar by which the class sum of `l` acts. -/
noncomputable def centralScalar (l : ConjClasses G) : ℂ :=
  Classical.choose
    (exists_scalar_of_central ρ (classSum (ConjClasses.carrier l).toFinset)
      (classSum_carrier_central l))

open Classical in
theorem centralScalar_spec (l : ConjClasses G) (v : V) :
    ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset) v
      = centralScalar ρ l • v :=
  Classical.choose_spec
    (exists_scalar_of_central ρ (classSum (ConjClasses.carrier l).toFinset)
      (classSum_carrier_central l)) v

open Classical in
/-- Central scalars multiply with the structure constants. -/
theorem centralScalar_mul (l1 l2 : ConjClasses G) :
    centralScalar ρ l1 * centralScalar ρ l2
      = ∑ l, (structConst (conjClass (classRep l1)) (conjClass (classRep l2))
          (classRep l) : ℂ) * centralScalar ρ l := by
  classical
  have hend : ρ.asAlgebraHom (classSum (ConjClasses.carrier l1).toFinset)
        * ρ.asAlgebraHom (classSum (ConjClasses.carrier l2).toFinset)
      = ∑ l, (structConst (conjClass (classRep l1)) (conjClass (classRep l2))
          (classRep l) : ℂ)
          • ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset) := by
    rw [carrier_toFinset, carrier_toFinset, ← map_mul, classSum_mul, map_sum]
    simp only [map_smul]
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hpoint : (ρ.asAlgebraHom (classSum (ConjClasses.carrier l1).toFinset)
        * ρ.asAlgebraHom (classSum (ConjClasses.carrier l2).toFinset)) v
      = (∑ l, (structConst (conjClass (classRep l1)) (conjClass (classRep l2))
          (classRep l) : ℂ)
          • ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset)) v :=
    congrArg (fun F : Module.End ℂ V => F v) hend
  rw [Module.End.mul_apply, LinearMap.sum_apply] at hpoint
  simp only [LinearMap.smul_apply, centralScalar_spec, smul_smul] at hpoint
  rw [← Finset.sum_smul] at hpoint
  have hsub : (centralScalar ρ l1 * centralScalar ρ l2
      - ∑ l, (structConst (conjClass (classRep l1)) (conjClass (classRep l2))
          (classRep l) : ℂ) * centralScalar ρ l) • v = 0 := by
    rw [sub_smul, hpoint, sub_self]
  rcases smul_eq_zero.mp hsub with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv

open Classical in
/-- The finite set of scalars spanning the integrality subalgebra. -/
noncomputable def scalarGens : Finset ℂ :=
  insert 1 (Finset.univ.image (centralScalar ρ))

open Classical in
theorem one_mem_scalarSpan : (1 : ℂ) ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) :=
  Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_self 1 _))

open Classical in
theorem scalar_mem_scalarSpan (l : ConjClasses G) :
    centralScalar ρ l ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) :=
  Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (Finset.mem_univ l))))

open Classical in
/-- Generator-generator products stay in the span. -/
theorem scalarGens_mul (a b : ℂ) (ha : a ∈ scalarGens ρ) (hb : b ∈ scalarGens ρ) :
    a * b ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := by
  classical
  rw [scalarGens, Finset.mem_insert, Finset.mem_image] at ha hb
  rcases ha with rfl | ⟨l1, _, rfl⟩ <;> rcases hb with rfl | ⟨l2, _, rfl⟩
  · simpa using one_mem_scalarSpan ρ
  · simp only [one_mul]
    exact scalar_mem_scalarSpan ρ l2
  · simp only [mul_one]
    exact scalar_mem_scalarSpan ρ l1
  · rw [centralScalar_mul]
    apply sum_mem
    intro l _
    have hsmul : ∀ (n : ℕ) (x : ℂ), (n : ℂ) * x = (n : ℤ) • x := by
      intro n x
      exact (zsmul_eq_mul x n).symm
    rw [hsmul]
    exact Submodule.smul_mem _ _ (scalar_mem_scalarSpan ρ l)

open Classical in
/-- The ℤ-span of the central scalars, as a subalgebra. -/
noncomputable def scalarSubalg : Subalgebra ℤ ℂ where
  carrier := ↑(Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ))
  mul_mem' := by
    intro x y hx hy
    have hx' : x ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := hx
    have hy' : y ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := hy
    suffices h : x * y ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) from h
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx'
    · intro z hz
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy'
      · intro w hw
        exact scalarGens_mul ρ z w (Finset.mem_coe.mp hz) (Finset.mem_coe.mp hw)
      · rw [mul_zero]
        exact Submodule.zero_mem _
      · intro a b ha hb iha ihb
        rw [mul_add]
        exact add_mem iha ihb
      · intro c b hb ih
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ _ ih
    · rw [zero_mul]
      exact Submodule.zero_mem _
    · intro a b ha hb iha ihb
      rw [add_mul]
      exact add_mem iha ihb
    · intro c a ha ih
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ _ ih
  one_mem' := one_mem_scalarSpan ρ
  add_mem' := by
    intro x y hx hy
    have hx' : x ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := hx
    have hy' : y ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := hy
    have h : x + y ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) :=
      Submodule.add_mem _ hx' hy'
    exact h
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' := by
    intro n
    have h1 : algebraMap ℤ ℂ n = n • (1 : ℂ) := by
      rw [Algebra.smul_def, mul_one]
    rw [h1]
    exact Submodule.smul_mem _ _ (one_mem_scalarSpan ρ)
end CentralScalar
end BurnsidePaqb
