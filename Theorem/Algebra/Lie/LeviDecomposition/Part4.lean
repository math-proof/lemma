/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.Algebra.Lie.LeviDecomposition.Part3
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem levi_finrank_quotient_comap
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (V W : LieSubmodule K L M) (hVW : V ⊔ W = ⊤) :
    Module.finrank K (V ⧸ W.comap V.incl) = Module.finrank K (M ⧸ W) := by
  change Module.finrank K (V ⧸ (W.comap V.incl).toSubmodule) =
    Module.finrank K (M ⧸ W.toSubmodule)
  let f : V →ₗ[K] M ⧸ W := W.toSubmodule.mkQ.comp V.toSubmodule.subtype
  have hker : LinearMap.ker f = (W.comap V.incl).toSubmodule := by
    ext v
    simp [f]
  have hsurj : Function.Surjective f := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ m =>
      have hm : m ∈ V ⊔ W := by
        rw [hVW]
        exact LieSubmodule.mem_top m
      rw [LieSubmodule.mem_sup] at hm
      obtain ⟨v, hv, w, hw, rfl⟩ := hm
      refine ⟨⟨v, hv⟩, ?_⟩
      change LieSubmodule.Quotient.mk (N := W) v =
        LieSubmodule.Quotient.mk (N := W) (v + w)
      apply (Submodule.Quotient.eq W.toSubmodule).2
      have hw' : w ∈ W.toSubmodule := hw
      simpa only [sub_add_cancel_left, neg_mem_iff] using hw'
  calc
    Module.finrank K (V ⧸ (W.comap V.incl).toSubmodule) =
        Module.finrank K (V ⧸ LinearMap.ker f) := by rw [hker]
    _ = Module.finrank K (LinearMap.range f) := f.quotKerEquivRange.finrank_eq
    _ = Module.finrank K (M ⧸ W) := by
      exact (LinearEquiv.ofTop (LinearMap.range f)
        (LinearMap.range_eq_top.mpr hsurj)).finrank_eq

theorem levi_isCompl_map_of_isCompl_comap
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (V W : LieSubmodule K L M) (hVW : V ⊔ W = ⊤)
    (U : LieSubmodule K L V) (hU : IsCompl (W.comap V.incl) U) :
    IsCompl W (U.map V.incl) := by
  constructor
  · rw [disjoint_iff]
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxU⟩ := hx
    change x ∈ U.toSubmodule.map V.toSubmodule.subtype at hxU
    rw [Submodule.mem_map] at hxU
    obtain ⟨u, hu, rfl⟩ := hxU
    have huW : u ∈ W.comap V.incl := hxW
    have hu0 : u ∈ (W.comap V.incl) ⊓ U := ⟨huW, hu⟩
    rw [hU.inf_eq_bot] at hu0
    change u = 0 at hu0
    change (u.1 : M) = 0
    exact congr_arg Subtype.val hu0
  · rw [codisjoint_iff]
    apply top_unique
    intro x _
    have hx : x ∈ V ⊔ W := by
      rw [hVW]
      exact LieSubmodule.mem_top x
    rw [LieSubmodule.mem_sup] at hx
    obtain ⟨v, hv, w, hw, rfl⟩ := hx
    let v' : V := ⟨v, hv⟩
    have hv' : v' ∈ (W.comap V.incl) ⊔ U := by
      rw [hU.sup_eq_top]
      exact LieSubmodule.mem_top v'
    rw [LieSubmodule.mem_sup] at hv'
    obtain ⟨a, ha, b, hb, hab⟩ := hv'
    rw [LieSubmodule.mem_sup]
    refine ⟨a.1 + w, W.add_mem ha hw, b.1, ?_, ?_⟩
    · exact LieSubmodule.mem_map_of_mem hb
    · apply_fun Subtype.val at hab
      dsimp [v'] at hab
      rw [← hab]
      abel

theorem levi_codim_one_complement_aux
    (n : ℕ) {K L M : Type*} [Field K] [CharZero K] [LieRing L]
    [LieAlgebra K L] [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (W : LieSubmodule K L M)
    (hquot : Module.finrank K (M ⧸ W) = 1) (_hlt : Module.finrank K W < n) :
    ∃ U : LieSubmodule K L M, IsCompl W U := by
  classical
  let I := LieModule.ker K L M
  let H := I.killingCompl
  let _ : LieAlgebra.IsKilling K L := inferInstance
  have hcompl : IsCompl I H := I.isCompl_killingCompl
  have hHkilling : LieAlgebra.IsKilling K H := levi_isKilling_killingCompl I
  let _ : LieAlgebra.IsKilling K H := hHkilling
  let _ : LieAlgebra.IsSemisimple K H := inferInstance
  by_cases hH0 : Module.finrank K H = 0
  · have hHbot : H = ⊥ := by
      rw [← LieSubmodule.toSubmodule_inj]
      exact Submodule.finrank_eq_zero.mp hH0
    have hItop : I = ⊤ := by
      have hs := hcompl.sup_eq_top
      rwa [hHbot, sup_bot_eq] at hs
    apply levi_exists_isCompl_of_trivial_action (W := W)
    intro x m
    have hx : x ∈ I := by
      rw [hItop]
      exact LieSubmodule.mem_top x
    change LieModule.toEnd K L M x = 0 at hx
    change LieModule.toEnd K L M x m = 0
    rw [hx]
    rfl
  · have hfaithful : LieModule.IsFaithful K H M :=
      levi_isFaithful_killingCompl_ker
    let _ : LieModule.IsFaithful K H M := hfaithful
    have hβ : (LieModule.traceForm K H M).Nondegenerate :=
      levi_traceForm_nondegenerate
    let c := leviCasimir hβ
    have hcL (x : L) : Commute c (LieModule.toEnd K L M x) := by
      have hx : x ∈ I ⊔ H := by
        rw [hcompl.sup_eq_top]
        exact LieSubmodule.mem_top x
      rw [LieSubmodule.mem_sup] at hx
      obtain ⟨i, hi, h, hh, rfl⟩ := hx
      have hi0 : LieModule.toEnd K L M i = 0 := by
        exact hi
      have hch := levi_casimir_commute hβ (⟨h, hh⟩ : H)
      change Commute c (LieModule.toEnd K L M h) at hch
      rw [map_add, hi0, zero_add]
      exact hch
    let V := leviZeroFitting c hcL
    let P := ⨅ k : ℕ, LinearMap.range (c ^ k)
    have hV : V.toSubmodule = ⨆ k : ℕ, LinearMap.ker (c ^ k) := by
      change c.maxGenEigenspace 0 = _
      rw [← Module.End.iSup_genEigenspace_eq]
      simp_rw [Module.End.genEigenspace_zero_nat]
    have hVP : IsCompl V.toSubmodule P := by
      rw [hV]
      exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow c
    have haction := levi_codim_one_action_mem W hquot
    have hcW : LinearMap.range c ≤ W.toSubmodule := by
      apply levi_casimir_range_le hβ W.toSubmodule
      intro x m
      exact haction x.1 m
    have hPW : P ≤ W.toSubmodule := by
      calc
        P ≤ LinearMap.range (c ^ 1) := iInf_le _ 1
        _ = LinearMap.range c := by rw [pow_one]
        _ ≤ W.toSubmodule := hcW
    have hPne : P ≠ ⊥ := by
      intro hP
      have hVtop : V.toSubmodule = ⊤ := by
        have hs := hVP.sup_eq_top
        rwa [hP, sup_bot_eq] at hs
      have hpoint : ∀ m : M, ∃ k : ℕ, (c ^ k) m = 0 := by
        intro m
        have hm : m ∈ c.maxGenEigenspace 0 := by
          change m ∈ V.toSubmodule
          rw [hVtop]
          exact Submodule.mem_top
        simpa using (Module.End.mem_maxGenEigenspace c 0 m).mp hm
      have hnil : IsNilpotent c :=
        ((LinearMap.charpoly_nilpotent_tfae c).out 3 1).mp hpoint
      have htrace0 : LinearMap.trace K M c = 0 :=
        (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
      rw [levi_trace_casimir hβ] at htrace0
      exact (Nat.cast_ne_zero.mpr hH0) htrace0
    have hVWsub : V.toSubmodule ⊔ W.toSubmodule = ⊤ := by
      apply top_unique
      rw [← hVP.sup_eq_top]
      exact sup_le_sup le_rfl hPW
    have hVW : V ⊔ W = ⊤ := by
      rw [← LieSubmodule.toSubmodule_inj]
      exact hVWsub
    have hInfLt : V.toSubmodule ⊓ W.toSubmodule < W.toSubmodule := by
      refine lt_of_le_of_ne inf_le_right ?_
      intro heq
      have hWV : W.toSubmodule ≤ V.toSubmodule := by
        rw [← heq]
        exact inf_le_left
      have hPV : P ≤ V.toSubmodule := hPW.trans hWV
      apply hPne
      rw [← le_bot_iff, ← hVP.inf_eq_bot]
      exact le_inf hPV le_rfl
    let W' := W.comap V.incl
    have hmapW' : W'.map V.incl = V ⊓ W := by
      ext x
      constructor
      · intro hx
        rw [LieSubmodule.mem_map] at hx
        obtain ⟨w, hw, rfl⟩ := hx
        exact ⟨w.2, hw⟩
      · rintro ⟨hxV, hxW⟩
        exact LieSubmodule.mem_map_of_mem (m := (⟨x, hxV⟩ : V)) hxW
    have hfinW' : Module.finrank K W' = Module.finrank K ↑(V ⊓ W) := by
      rw [← hmapW']
      exact (LieSubmodule.equivMapOfInjective W' V.injective_incl).toLinearEquiv.finrank_eq
    have hlt' : Module.finrank K W' < Module.finrank K W := by
      rw [hfinW']
      exact Submodule.finrank_lt_finrank_of_lt hInfLt
    have hquot' : Module.finrank K (V ⧸ W') = 1 := by
      rw [levi_finrank_quotient_comap V W hVW]
      exact hquot
    obtain ⟨U, hU⟩ := levi_codim_one_complement_aux (Module.finrank K W) W' hquot' hlt'
    exact ⟨U.map V.incl, levi_isCompl_map_of_isCompl_comap V W hVW U hU⟩
termination_by n
decreasing_by exact _hlt

theorem levi_codim_one_complement
    {K L M : Type*} [Field K] [CharZero K] [LieRing L]
    [LieAlgebra K L] [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (W : LieSubmodule K L M)
    (hquot : Module.finrank K (M ⧸ W) = 1) :
    ∃ U : LieSubmodule K L M, IsCompl W U :=
  levi_codim_one_complement_aux (Module.finrank K W + 1) W hquot (Nat.lt_succ_self _)

end LeviDecomposition
