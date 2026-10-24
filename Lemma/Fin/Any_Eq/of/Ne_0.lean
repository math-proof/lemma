import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.HighestWeightModules


/--
[ChevalleyData.sl2_weight_integrality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HighestWeightModules.lean)
-/
@[path]
private lemma main
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R 𝔤}
  {Δ : TriangularDecomposition R 𝔤}
  {chev : ChevalleyData Δ}
  {i : Fin chev.rank}
  {V : Type u_mod}
  [AddCommGroup V]
  [Module R V]
  [LieRingModule 𝔤 V]
  [LieModule R 𝔤 V]
  [IsNoetherian R V]
  [Module.IsTorsionFree R V]
  [IsDomain R]
  [CharZero R]
  {v : V}
  {μ : R}
-- given
  (hv : v ≠ 0)
  (he : ⁅chev.posGen i, v⁆ = 0)
  (hh : ⁅(chev.simpleCoroot i : 𝔤), v⁆ = μ • v) :
-- imply
  ∃ (n : ℕ), μ = (n : R) := by
-- proof
  by_cases hhz : (chev.simpleCoroot i : 𝔤) = 0
  ·
    have hμv : μ • v = 0 := by rw [← hh, hhz, zero_lie]
    have hμ0 : μ = 0 := by
      by_contra hμ
      have hreg : IsRegular μ :=
        ⟨fun a b hab => mul_left_cancel₀ hμ hab,
          fun a b hab => mul_right_cancel₀ hμ hab⟩
      have hsmul : IsSMulRegular V μ :=
        Module.IsTorsionFree.isSMulRegular (M := V) hreg
      exact hv (hsmul (show μ • v = μ • 0 by simp [hμv]))
    exact ⟨0, by simp [hμ0]⟩
  ·
    have t : IsSl2Triple (chev.simpleCoroot i : 𝔤) (chev.posGen i) (chev.negGen i) :=
      IsSl2Triple.mk hhz
        (chev.bracket_ef i)
        (by rw [two_nsmul]; exact chev.bracket_he i)
        (by rw [two_nsmul]; exact chev.bracket_hf i)
    have P : t.HasPrimitiveVectorWith v μ :=
      IsSl2Triple.HasPrimitiveVectorWith.mk hv hh he
    exact P.exists_nat

/--
[exercise_8_11](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HighestWeightModules.lean)
-/
private lemma exercise_8_11
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R 𝔤}
  {Δ : TriangularDecomposition R 𝔤}
  {chev : ChevalleyData Δ}
  {wt : Δ.𝔥 →ₗ[R] R}
  {V : Type u_mod}
  [AddCommGroup V]
  [Module R V]
  [LieRingModule 𝔤 V]
  [LieModule R 𝔤 V]
  [IsNoetherian R V]
  [Module.IsTorsionFree R V]
  [IsDomain R]
  [CharZero R]
  {i : Fin chev.rank}
-- given
  (hV : IsHighestWeightModule Δ V wt) :
-- imply
  ∃ (n : ℕ), wt (chev.simpleCoroot i) = (n : R) := by
-- proof
  set v := hV.highestWeightVec with hv_def
  set μ := wt (chev.simpleCoroot i) with hμ_def
  have he_v : ⁅chev.posGen i, v⁆ = 0 :=
    hV.npos_action ⟨chev.posGen i, chev.posGen_mem i⟩
  have hh_v : ⁅(chev.simpleCoroot i : 𝔤), v⁆ = μ • v :=
    hV.cartan_action (chev.simpleCoroot i)
  exact chev.sl2_weight_integrality i v hV.hwv_ne_zero he_v μ hh_v


-- created on 2026-10-23
-- updated on 2026-10-24
