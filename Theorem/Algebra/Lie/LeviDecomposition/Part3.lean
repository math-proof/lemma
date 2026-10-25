/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.Algebra.Lie.LeviDecomposition.Part2
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem levi_trace_casimir
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Free K M] [Module.Finite K M]
    (hβ : (LieModule.traceForm K L M).Nondegenerate) :
    LinearMap.trace K M (leviCasimir hβ) = (Module.finrank K L : K) := by
  classical
  let b := Module.Free.chooseBasis K L
  change LinearMap.trace K M (∑ i, LieModule.toEnd K L M (b i) *
    LieModule.toEnd K L M ((LieModule.traceForm K L M).dualBasis hβ b i)) = _
  rw [map_sum]
  simp_rw [Module.End.mul_eq_comp]
  simp_rw [← LieModule.traceForm_apply_apply]
  simp_rw [LinearMap.BilinForm.apply_dualBasis_right hβ
    (LinearMap.BilinForm.isSymm_iff.mpr (LieModule.traceForm_isSymm K L M)) b]
  simp [Module.finrank_eq_card_basis b]

theorem levi_lie_dualBasis
    {K L M ι : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Fintype ι] [DecidableEq ι]
    (hβ : (LieModule.traceForm K L M).Nondegenerate)
    (b : Module.Basis ι K L) (x : L) (i : ι) :
    ⁅x, (LieModule.traceForm K L M).dualBasis hβ b i⁆ =
      -∑ j, b.repr ⁅x, b j⁆ i •
        (LieModule.traceForm K L M).dualBasis hβ b j := by
  let d := (LieModule.traceForm K L M).dualBasis hβ b
  apply d.repr.injective
  ext j
  rw [LinearMap.BilinForm.dualBasis_repr_apply]
  rw [LieModule.traceForm_apply_lie_apply']
  rw [← levi_repr_eq_dual hβ b ⁅x, b j⁆ i]
  simp [d, Finsupp.single_apply]

theorem levi_casimir_commute
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Free K M] [Module.Finite K M]
    (hβ : (LieModule.traceForm K L M).Nondegenerate) (x : L) :
    Commute (leviCasimir hβ) (LieModule.toEnd K L M x) := by
  classical
  let b := Module.Free.chooseBasis K L
  let d := (LieModule.traceForm K L M).dualBasis hβ b
  let ρ := LieModule.toEnd K L M
  change Commute (∑ i, ρ (b i) * ρ (d i)) (ρ x)
  rw [commute_iff_eq]
  rw [← sub_eq_zero]
  calc
    (∑ i, ρ (b i) * ρ (d i)) * ρ x - ρ x * (∑ i, ρ (b i) * ρ (d i)) =
        -(∑ i, (ρ ⁅x, b i⁆ * ρ (d i) + ρ (b i) * ρ ⁅x, d i⁆)) := by
          rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [LieHom.map_lie ρ, LieHom.map_lie ρ, Ring.lie_def, Ring.lie_def]
          noncomm_ring
    _ = 0 := by
      have hxb (i) : ρ ⁅x, b i⁆ =
          ∑ j, b.repr ⁅x, b i⁆ j • ρ (b j) := by
        conv_lhs => rw [← levi_sum_repr b ⁅x, b i⁆]
        rw [map_sum]
        simp_rw [map_smul]
      have hxd (i) : ρ ⁅x, d i⁆ =
          -∑ j, b.repr ⁅x, b j⁆ i • ρ (d j) := by
        rw [levi_lie_dualBasis hβ b x i]
        rw [map_neg, map_sum]
        simp_rw [map_smul]
        rfl
      rw [Finset.sum_add_distrib]
      simp_rw [hxb, hxd]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
        mul_neg, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      simp

theorem levi_casimir_range_le
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Free K M] [Module.Finite K M]
    (hβ : (LieModule.traceForm K L M).Nondegenerate) (W : Submodule K M)
    (hW : ∀ (x : L) (m : M), LieModule.toEnd K L M x m ∈ W) :
    LinearMap.range (leviCasimir hβ) ≤ W := by
  classical
  rintro _ ⟨m, rfl⟩
  let b := Module.Free.chooseBasis K L
  let d := (LieModule.traceForm K L M).dualBasis hβ b
  change (∑ i, LieModule.toEnd K L M (b i) * LieModule.toEnd K L M (d i)) m ∈ W
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i _
  rw [Module.End.mul_apply]
  exact hW (b i) _

theorem levi_isKilling_killingCompl
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSemisimple K L] (I : LieIdeal K L) :
    LieAlgebra.IsKilling K I.killingCompl := by
  let _ : LieAlgebra.IsKilling K L := inferInstance
  let H := I.killingCompl
  have hcompl : IsCompl I H := I.isCompl_killingCompl
  have hB := LieAlgebra.IsKilling.killingForm_nondegenerate K L
  have hrefl := (LieModule.traceForm_isSymm K L L).isRefl
  have horth : (killingForm K L).orthogonal H.toSubmodule = I.toSubmodule := by
    change (killingForm K L).orthogonal
      ((killingForm K L).orthogonal I.toSubmodule) = I.toSubmodule
    exact LinearMap.BilinForm.orthogonal_orthogonal hB hrefl I.toSubmodule
  have hdisj : Disjoint H.toSubmodule
      ((killingForm K L).orthogonal H.toSubmodule) := by
    rw [horth]
    exact LieSubmodule.disjoint_toSubmodule.mpr hcompl.disjoint.symm
  have hres : ((killingForm K L).restrict H.toSubmodule).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal
      (killingForm K L) hrefl hdisj
  have hk : (killingForm K H).Nondegenerate := by
    rw [LieIdeal.killingForm_eq]
    exact hres
  refine LieAlgebra.IsKilling.mk ?_
  rw [eq_bot_iff]
  intro x hx
  rw [LieSubmodule.mem_bot]
  apply hk.2 x
  intro y
  exact (LieIdeal.mem_killingCompl K H ⊤).mp hx y (LieSubmodule.mem_top y)

theorem levi_isFaithful_killingCompl_ker
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] :
    LieModule.IsFaithful K (LieModule.ker K L M).killingCompl M := by
  let I := LieModule.ker K L M
  let H := I.killingCompl
  let _ : LieAlgebra.IsKilling K L := inferInstance
  have hcompl : IsCompl I H := I.isCompl_killingCompl
  refine ⟨?_⟩
  intro x y hxy
  apply Subtype.ext
  change LieModule.toEnd K L M x.1 = LieModule.toEnd K L M y.1 at hxy
  have hker : x.1 - y.1 ∈ I := by
    change LieModule.toEnd K L M (x.1 - y.1) = 0
    rw [map_sub, sub_eq_zero]
    exact hxy
  have hH : x.1 - y.1 ∈ H := H.sub_mem x.2 y.2
  have hz : x.1 - y.1 ∈ I ⊓ H := ⟨hker, hH⟩
  rw [hcompl.inf_eq_bot] at hz
  change x.1 - y.1 = 0 at hz
  exact sub_eq_zero.mp hz

theorem levi_lie_top_eq_top
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieAlgebra.IsSemisimple K L] :
    ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ = ⊤ := by
  apply top_unique
  calc
    (⊤ : LieIdeal K L) = sSup {I : LieIdeal K L | IsAtom I} :=
      LieAlgebra.IsSemisimple.sSup_atoms_eq_top.symm
    _ ≤ ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ := by
      apply sSup_le
      intro I hI
      rw [← lie_eq_self_of_isAtom_of_nonabelian I hI
        (LieAlgebra.IsSemisimple.non_abelian_of_isAtom I hI)]
      exact LieSubmodule.mono_lie le_top le_top

theorem levi_codim_one_action_mem
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [LieAlgebra.IsSemisimple K L] [AddCommGroup M] [Module K M]
    [LieRingModule L M] [LieModule K L M] [Module.Finite K M]
    (W : LieSubmodule K L M) (hW : Module.finrank K (M ⧸ W) = 1) :
    ∀ (x : L) (m : M), ⁅x, m⁆ ∈ W := by
  let Q := M ⧸ W
  have hendcomm (f g : Module.End K Q) : Commute f g := by
    obtain ⟨a, ha, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hW f
    obtain ⟨b, hb, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hW g
    rw [ha, hb]
    ext q
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    rw [mul_comm]
  have hbracket (x y : L) : LieModule.toEnd K L Q ⁅x, y⁆ = 0 := by
    rw [LieHom.map_lie, Ring.lie_def, (hendcomm _ _).eq, sub_self]
  have hle : ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ ≤ LieModule.ker K L Q := by
    rw [LieSubmodule.lie_le_iff]
    intro x _ y _
    change LieModule.toEnd K L Q ⁅x, y⁆ = 0
    exact hbracket x y
  have hker : LieModule.ker K L Q = ⊤ := by
    apply top_unique
    rw [← levi_lie_top_eq_top]
    exact hle
  intro x m
  apply (LieSubmodule.Quotient.mk_eq_zero W).mp
  rw [LieModuleHom.map_lie]
  have hx : x ∈ LieModule.ker K L Q := by
    rw [hker]
    exact LieSubmodule.mem_top x
  change LieModule.toEnd K L Q x ((LieSubmodule.Quotient.mk' W) m) = 0
  change LieModule.toEnd K L Q x = 0 at hx
  rw [hx]
  rfl

theorem levi_exists_isCompl_of_trivial_action
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (htriv : ∀ (x : L) (m : M), ⁅x, m⁆ = 0) (W : LieSubmodule K L M) :
    ∃ U : LieSubmodule K L M, IsCompl W U := by
  obtain ⟨U, hU⟩ := W.toSubmodule.exists_isCompl
  let U' : LieSubmodule K L M :=
    { __ := U
      lie_mem := by
        intro x m _
        rw [htriv]
        exact zero_mem U }
  exact ⟨U', LieSubmodule.isCompl_toSubmodule.mp hU⟩

end LeviDecomposition
