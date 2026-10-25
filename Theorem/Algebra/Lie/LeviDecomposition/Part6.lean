/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.Algebra.Lie.LeviDecomposition.Part5
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem leviHomScalar_apply
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥)
    (f : leviHomScalarMaps W) (w : W) :
    f.1 w = leviHomScalar W hW f • w :=
  Classical.choose_spec f.2 w

theorem leviHomScalar_ker
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    LinearMap.ker (leviHomScalar W hW) =
      (leviHomVanishing W).toSubmodule.comap
        (leviHomScalarMaps W).toSubmodule.subtype := by
  ext f
  constructor
  · intro hf
    change leviHomScalar W hW f = 0 at hf
    change ∀ w : W, f.1 w = 0
    intro w
    rw [leviHomScalar_apply W hW f w, hf, zero_smul]
  · intro hf
    change leviHomScalar W hW f = 0
    apply levi_scalar_unique W hW
    intro w
    rw [zero_smul]
    exact (leviHomScalar_apply W hW f w).symm.trans (hf w)

theorem leviHomScalar_surjective
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    Function.Surjective (leviHomScalar W hW) := by
  obtain ⟨Q, hQ⟩ := W.toSubmodule.exists_isCompl
  let p : M →ₗ[K] W := W.toSubmodule.projectionOnto Q hQ
  have hp (w : W) : p w = w := by
    exact Submodule.projectionOnto_apply_left hQ w
  let pv : leviHomScalarMaps W :=
    ⟨p, 1, fun w ↦ by rw [hp, one_smul]⟩
  have hpv : leviHomScalar W hW pv = 1 := by
    apply levi_scalar_unique W hW
    intro w
    rw [one_smul]
    exact (leviHomScalar_apply W hW pv w).symm.trans (hp w)
  intro a
  refine ⟨a • pv, ?_⟩
  rw [LinearMap.map_smul, hpv, smul_eq_mul, mul_one]

theorem leviHomScalarMaps_quotient_finrank
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    Module.finrank K
        (leviHomScalarMaps W ⧸
          (leviHomVanishing W).comap (leviHomScalarMaps W).incl) = 1 := by
  let s := leviHomScalar W hW
  have hsKer : LinearMap.ker s =
      ((leviHomVanishing W).comap (leviHomScalarMaps W).incl).toSubmodule := by
    exact leviHomScalar_ker W hW
  have hsRange : LinearMap.range s = ⊤ :=
    LinearMap.range_eq_top.mpr (leviHomScalar_surjective W hW)
  change Module.finrank K
      (leviHomScalarMaps W ⧸
        ((leviHomVanishing W).comap (leviHomScalarMaps W).incl).toSubmodule) = 1
  rw [← hsKer, s.quotKerEquivRange.finrank_eq, hsRange]
  rw [finrank_top]
  exact Module.finrank_self K

theorem levi_lie_mem_HomVanishing_of_mem_scalarMaps
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (f : leviHomScalarMaps W) (x : L) :
    ⁅x, (f.1 : M →ₗ[K] W)⁆ ∈ leviHomVanishing W := by
  obtain ⟨a, ha⟩ := f.2
  intro w
  rw [LieHom.lie_apply, ha, lie_smul]
  have haw := ha (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W)
  rw [haw]
  have hxw : ⁅x, w⁆ = (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W) := rfl
  rw [hxw, sub_self]

/-- Weyl's complete reducibility theorem for finite-dimensional modules over a
semisimple Lie algebra in characteristic zero. -/
theorem _root_.LieModule.exists_isCompl_of_isSemisimple
    {K L M : Type*} [Field K] [CharZero K] [LieRing L]
    [LieAlgebra K L] [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (W : LieSubmodule K L M) :
    ∃ U : LieSubmodule K L M, IsCompl W U := by
  by_cases hW : W = ⊥
  · subst W
    exact ⟨⊤, isCompl_bot_top⟩
  let V := leviHomScalarMaps W
  let Z := (leviHomVanishing W).comap V.incl
  have hfin : Module.finrank K (V ⧸ Z) = 1 :=
    leviHomScalarMaps_quotient_finrank W hW
  obtain ⟨T, hT⟩ := levi_codim_one_complement Z hfin
  obtain ⟨Q, hQ⟩ := W.toSubmodule.exists_isCompl
  let p : M →ₗ[K] W := W.toSubmodule.projectionOnto Q hQ
  have hp (w : W) : p w = w := Submodule.projectionOnto_apply_left hQ w
  let pv : V := ⟨p, 1, fun w ↦ by rw [hp, one_smul]⟩
  have hpvScalar : leviHomScalar W hW pv = 1 := by
    apply levi_scalar_unique W hW
    intro w
    rw [one_smul]
    exact (leviHomScalar_apply W hW pv w).symm.trans (hp w)
  have hpvMem : pv ∈ Z ⊔ T := by
    rw [hT.sup_eq_top]
    trivial
  rw [LieSubmodule.mem_sup] at hpvMem
  obtain ⟨z, hz, t, ht, hzt⟩ := hpvMem
  have hzScalar : leviHomScalar W hW z = 0 := by
    have hzKer : z ∈ LinearMap.ker (leviHomScalar W hW) := by
      rw [leviHomScalar_ker W hW]
      exact hz
    exact hzKer
  have htScalar : leviHomScalar W hW t = 1 := by
    have h := congrArg (fun f : V ↦ leviHomScalar W hW f) hzt
    rw [LinearMap.map_add, hzScalar, zero_add, hpvScalar] at h
    exact h
  have htApply (w : W) : t.1 w = w := by
    rw [leviHomScalar_apply W hW t w, htScalar, one_smul]
  have htInvariant (x : L) : ⁅x, (t.1 : M →ₗ[K] W)⁆ = 0 := by
    have hxZ : ⁅x, t⁆ ∈ Z := by
      exact levi_lie_mem_HomVanishing_of_mem_scalarMaps W t x
    have hxT : ⁅x, t⁆ ∈ T := T.lie_mem ht
    have hxBot : ⁅x, t⁆ ∈ (⊥ : LieSubmodule K L V) := by
      rw [← hT.inf_eq_bot]
      exact ⟨hxZ, hxT⟩
    have hxZero : ⁅x, t⁆ = 0 := by simpa using hxBot
    exact congrArg Subtype.val hxZero
  let U : LieSubmodule K L M :=
    { carrier := {m | t.1 m = 0}
      zero_mem' := LinearMap.map_zero t.1
      add_mem' := by
        intro a b ha hb
        change t.1 (a + b) = 0
        rw [LinearMap.map_add, ha, hb, add_zero]
      smul_mem' := by
        intro a m hm
        change t.1 (a • m) = 0
        rw [LinearMap.map_smul, hm, smul_zero]
      lie_mem := by
        intro x m hm
        have h := congrArg (fun f : M →ₗ[K] W ↦ f m) (htInvariant x)
        rw [LieHom.lie_apply, hm, lie_zero, zero_sub] at h
        exact neg_eq_zero.mp h }
  refine ⟨U, ?_⟩
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro m hm
    have htm : t.1 m = 0 := hm.2
    have hrest := htApply (⟨m, hm.1⟩ : W)
    have hm0 : m = 0 := by
      have h := congrArg Subtype.val hrest
      rw [htm] at h
      exact h.symm
    change m = 0
    exact hm0
  · rw [codisjoint_iff, eq_top_iff]
    intro m _
    rw [LieSubmodule.mem_sup]
    refine ⟨(t.1 m).1, (t.1 m).2, m - (t.1 m).1, ?_, ?_⟩
    · change t.1 (m - (t.1 m).1) = 0
      rw [LinearMap.map_sub, htApply (t.1 m), sub_self]
    · abel

end LeviDecomposition
