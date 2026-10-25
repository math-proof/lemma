/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.Algebra.Lie.LeviDecomposition.Part11
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem leviMapRestrict_surjective
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L')
    (hf : Function.Surjective f) (I : LieIdeal K L) :
    Function.Surjective (leviMapRestrict f I) := by
  intro y
  obtain ⟨x, hx⟩ := LieIdeal.mem_map_of_surjective hf y.2
  refine ⟨x, ?_⟩
  exact Subtype.ext hx

theorem levi_isSolvable_map
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L')
    (hf : Function.Surjective f) (I : LieIdeal K L)
    [LieAlgebra.IsSolvable I] : LieAlgebra.IsSolvable (I.map f) :=
  (leviMapRestrict_surjective f hf I).lieAlgebra_isSolvable

theorem levi_radical_quotient
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] (I : LieIdeal K L)
    (hI : I ≤ LieAlgebra.radical K L) :
    (LieAlgebra.radical K L).map (leviQuotientMk I) =
      LieAlgebra.radical K (L ⧸ I) := by
  let q := leviQuotientMk I
  have hq : Function.Surjective q := leviQuotientMk_surjective I
  apply le_antisymm
  · rw [← LieIdeal.solvable_iff_le_radical]
    exact levi_isSolvable_map q hq (LieAlgebra.radical K L)
  · change LieAlgebra.radical K (L ⧸ I) ≤
      (LieAlgebra.radical K L).map q
    have hmapComap :
        ((LieAlgebra.radical K (L ⧸ I)).comap q).map q =
          LieAlgebra.radical K (L ⧸ I) := by
      rw [LieIdeal.map_comap_eq (q.isIdealMorphism_of_surjective hq)]
      rw [q.idealRange_eq_top_of_surjective hq, top_inf_eq]
    rw [← hmapComap]
    apply LieIdeal.map_mono
    rw [← LieIdeal.solvable_iff_le_radical]
    have hker : q.ker = I := leviQuotientMk_ker I
    have _ : LieAlgebra.IsSolvable q.ker := by
      rw [hker]
      exact LieAlgebra.le_solvable_ideal_solvable hI inferInstance
    exact levi_isSolvable_comap q hq (LieAlgebra.radical K (L ⧸ I))

theorem levi_radical_quotient_radical_eq_bot
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] :
    LieAlgebra.radical K (L ⧸ LieAlgebra.radical K L) = ⊥ := by
  rw [← levi_radical_quotient (LieAlgebra.radical K L) le_rfl]
  rw [LieIdeal.map_eq_bot_iff, leviQuotientMk_ker]

theorem levi_quotient_radical_isSemisimple
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] :
    LieAlgebra.IsSemisimple K (L ⧸ LieAlgebra.radical K L) := by
  let _ : LieAlgebra.HasTrivialRadical K (L ⧸ LieAlgebra.radical K L) :=
    ⟨levi_radical_quotient_radical_eq_bot⟩
  exact inferInstance

theorem levi_split_central_kernel
    {K L G : Type*} [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [Module.Finite K L]
    [LieRing G] [LieAlgebra K G] [Module.Finite K G]
    [LieAlgebra.IsSemisimple K G] (q : L →ₗ⁅K⁆ G)
    (hq : Function.Surjective q)
    (hcentral : ∀ x ∈ q.ker, ∀ y : L, ⁅x, y⁆ = 0) :
    ∃ S : LieSubalgebra K L, LieAlgebra.IsSemisimple K S ∧
      ((q.ker : Submodule K L) + (S : Submodule K L) = ⊤) ∧
      ((q.ker : Submodule K L) ⊓ (S : Submodule K L) = ⊥) := by
  let rangeIncl : q.range →ₗ⁅K⁆ G := q.range.incl
  have hRangeIncl : Function.Bijective rangeIncl := by
    constructor
    · intro x y h
      exact Subtype.ext h
    · intro y
      obtain ⟨x, rfl⟩ := hq y
      exact ⟨⟨q x, LieHom.mem_range_self q x⟩, rfl⟩
  let eRange : q.range ≃ₗ⁅K⁆ G := LieEquiv.ofBijective rangeIncl hRangeIncl
  let eQuot : (L ⧸ q.ker) ≃ₗ⁅K⁆ G := q.quotKerEquivRange.trans eRange
  let _ : LieAlgebra.IsKilling K (L ⧸ q.ker) :=
    LieAlgebra.isKilling_of_equiv eQuot.symm
  let _ : LieAlgebra.IsSemisimple K (L ⧸ q.ker) := inferInstance
  have hkerAction : ∀ x ∈ q.ker, ∀ y : L, ⁅x, y⁆ = 0 := hcentral
  obtain ⟨U, hU⟩ :=
    levi_factor_exists_isCompl q.ker hkerAction (q.ker : LieSubmodule K L L)
  let qU : U →ₗ⁅K⁆ G := q.comp (LieSubalgebra.incl (LieIdeal.toLieSubalgebra K L U))
  have hqUInjective : Function.Injective qU := by
    intro x y hxy
    apply Subtype.ext
    have hdiffKer : x.1 - y.1 ∈ q.ker := by
      rw [LieHom.mem_ker]
      rw [map_sub]
      change qU x - qU y = 0
      rw [hxy, sub_self]
    have hdiffU : x.1 - y.1 ∈ U := U.sub_mem x.2 y.2
    have hdiffBot : x.1 - y.1 ∈ (⊥ : LieSubmodule K L L) := by
      rw [← hU.inf_eq_bot]
      exact ⟨hdiffKer, hdiffU⟩
    have hdiff : x.1 - y.1 = 0 := by simpa using hdiffBot
    exact sub_eq_zero.mp hdiff
  have hqUSurjective : Function.Surjective qU := by
    intro y
    obtain ⟨x, hx⟩ := hq y
    have hxSup : x ∈ q.ker ⊔ U := by
      rw [hU.sup_eq_top]
      trivial
    rw [LieSubmodule.mem_sup] at hxSup
    obtain ⟨z, hz, u, hu, hzu⟩ := hxSup
    refine ⟨⟨u, hu⟩, ?_⟩
    change q u = y
    have hz0 : q z = 0 := LieHom.mem_ker.mp hz
    calc
      q u = q (z + u) := by rw [map_add, hz0, zero_add]
      _ = q x := congrArg q hzu
      _ = y := hx
  let eU : U ≃ₗ⁅K⁆ G := LieEquiv.ofBijective qU ⟨hqUInjective, hqUSurjective⟩
  let _ : LieAlgebra.IsKilling K U := LieAlgebra.isKilling_of_equiv eU.symm
  let _ : LieAlgebra.IsSemisimple K U := inferInstance
  let S := LieIdeal.toLieSubalgebra K L U
  let UtoS : U →ₗ⁅K⁆ S :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      map_lie' := by
        intro x y
        apply Subtype.ext
        rfl }
  have hUtoS : Function.Bijective UtoS := by
    constructor
    · intro x y h
      have h' := congrArg (fun z : S ↦ z.1) h
      change x.1 = y.1 at h'
      exact Subtype.ext h'
    · intro y
      refine ⟨⟨y.1, y.2⟩, ?_⟩
      apply Subtype.ext
      rfl
  let eUS : U ≃ₗ⁅K⁆ S := LieEquiv.ofBijective UtoS hUtoS
  let _ : LieAlgebra.IsKilling K S := LieAlgebra.isKilling_of_equiv eUS
  let _ : LieAlgebra.IsSemisimple K S := inferInstance
  refine ⟨S, inferInstance, ?_, ?_⟩
  · rw [← LieSubmodule.isCompl_toSubmodule] at hU
    exact hU.sup_eq_top
  · rw [← LieSubmodule.isCompl_toSubmodule] at hU
    exact hU.inf_eq_bot

theorem levi_abelian_radical_map
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] :
    let R := LieAlgebra.radical K L
    let V := leviHomScalarMaps (L := L) R
    let P : LieSubmodule K L V := ⁅R, ⊤⁆
    ∃ f : V, (∀ r : R, f.1 r = r) ∧ (∀ x : L, ⁅x, f⁆ ∈ P) := by
  let R := LieAlgebra.radical K L
  let V := leviHomScalarMaps (L := L) R
  let Z := (leviHomVanishing R).comap V.incl
  let P : LieSubmodule K L V := ⁅R, ⊤⁆
  have hPZ : P ≤ Z := by
    rw [LieSubmodule.lie_le_iff]
    intro x hx f _
    exact levi_lie_mem_HomVanishing_of_mem_scalarMaps R f x
  let Wbar := Z.map (LieSubmodule.Quotient.mk' P)
  have hRaction : ∀ x ∈ R, ∀ m : V ⧸ P, ⁅x, m⁆ = 0 := by
    intro x hx m
    induction m using Submodule.Quotient.induction_on with
    | _ f =>
      change LieSubmodule.Quotient.mk' P ⁅x, f⁆ = 0
      rw [LieSubmodule.Quotient.mk_eq_zero]
      exact LieSubmodule.lie_mem_lie hx (LieSubmodule.mem_top f)
  let _ : LieAlgebra.IsSemisimple K (L ⧸ R) :=
    levi_quotient_radical_isSemisimple
  obtain ⟨C, hC⟩ := levi_factor_exists_isCompl R hRaction Wbar
  obtain ⟨Q, hQ⟩ := R.toSubmodule.exists_isCompl
  let p : L →ₗ[K] R := R.toSubmodule.projectionOnto Q hQ
  have hp (r : R) : p r = r := Submodule.projectionOnto_apply_left hQ r
  let pv : V := ⟨p, 1, fun r ↦ by rw [hp, one_smul]⟩
  let pvbar : V ⧸ P := LieSubmodule.Quotient.mk' P pv
  have hpvbar : pvbar ∈ Wbar ⊔ C := by
    rw [hC.sup_eq_top]
    trivial
  rw [LieSubmodule.mem_sup] at hpvbar
  obtain ⟨z, hz, c, hc, hzc⟩ := hpvbar
  rw [LieSubmodule.mem_map] at hz
  obtain ⟨z₀, hz₀, hz₀eq⟩ := hz
  let f : V := pv - z₀
  have hfbar : LieSubmodule.Quotient.mk' P f = c := by
    change LieSubmodule.Quotient.mk' P (pv - z₀) = c
    rw [map_sub, hz₀eq]
    change pvbar - z = c
    rw [← hzc]
    abel
  have hfApply (r : R) : f.1 r = r := by
    change (pv.1 - z₀.1) r = r
    rw [LinearMap.sub_apply, hp]
    have hz₀r : z₀.1 r = 0 := hz₀ r
    rw [hz₀r, sub_zero]
  refine ⟨f, hfApply, ?_⟩
  intro x
  have hxcC : ⁅x, c⁆ ∈ C := C.lie_mem hc
  have hxcW : ⁅x, c⁆ ∈ Wbar := by
    rw [← hfbar, ← LieModuleHom.map_lie]
    exact LieSubmodule.mem_map_of_mem
      (levi_lie_mem_HomVanishing_of_mem_scalarMaps R f x)
  have hxcBot : ⁅x, c⁆ ∈ (⊥ : LieSubmodule K L (V ⧸ P)) := by
    rw [← hC.inf_eq_bot]
    exact ⟨hxcW, hxcC⟩
  have hxcZero : ⁅x, c⁆ = 0 := by simpa using hxcBot
  rw [← LieSubmodule.Quotient.mk_eq_zero]
  rw [LieModuleHom.map_lie, hfbar, hxcZero]

end LeviDecomposition
