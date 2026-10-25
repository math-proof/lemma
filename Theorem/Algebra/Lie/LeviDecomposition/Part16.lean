/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.Algebra.Lie.LeviDecomposition.Part15
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem leviSubalgebraComapKerToKer_injective
    {K L G : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing G] [LieAlgebra K G] (q : L →ₗ⁅K⁆ G) (T : LieSubalgebra K G) :
    Function.Injective (leviSubalgebraComapKerToKer q T) := by
  intro x y h
  have hxy := congrArg (fun z : q.ker ↦ z.1) h
  change x.1.1 = y.1.1 at hxy
  exact Subtype.ext (Subtype.ext hxy)

theorem levi_radical_comap_semisimple
    {K L G : Type*} [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [Module.Finite K L]
    [LieRing G] [LieAlgebra K G] [Module.Finite K G] (q : L →ₗ⁅K⁆ G)
    (hq : Function.Surjective q) (T : LieSubalgebra K G)
    [LieAlgebra.IsSemisimple K T] [LieAlgebra.IsSolvable q.ker] :
    LieAlgebra.radical K (T.comap q) = (leviSubalgebraComapMap q T).ker := by
  let qT := leviSubalgebraComapMap q T
  have hqT : Function.Surjective qT := leviSubalgebraComapMap_surjective q hq T
  have _ : LieAlgebra.IsSolvable qT.ker :=
    (leviSubalgebraComapKerToKer_injective q T).lieAlgebra_isSolvable
  apply le_antisymm
  · rw [← LieIdeal.map_eq_bot_iff]
    have hsolv : LieAlgebra.IsSolvable ((LieAlgebra.radical K (T.comap q)).map qT) :=
      levi_isSolvable_map qT hqT (LieAlgebra.radical K (T.comap q))
    have hle : (LieAlgebra.radical K (T.comap q)).map qT ≤
        LieAlgebra.radical K T :=
      (LieIdeal.solvable_iff_le_radical (R := K) (L := T) _).mp hsolv
    simpa using hle
  · exact (LieIdeal.solvable_iff_le_radical (R := K) (L := T.comap q) _).mp inferInstance

theorem levi_derived_radical_lt
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L]
    (hR : ¬ IsLieAbelian (LieAlgebra.radical K L)) :
    ⁅LieAlgebra.radical K L, LieAlgebra.radical K L⁆ <
      LieAlgebra.radical K L := by
  let R := LieAlgebra.radical K L
  let D : LieIdeal K L := ⁅R, R⁆
  have hRne : R ≠ ⊥ := by
    intro h
    apply hR
    rw [show LieAlgebra.radical K L = ⊥ from h]
    infer_instance
  let _ : Nontrivial R :=
    (LieSubmodule.nontrivial_iff_ne_bot K L L).mpr hRne
  have hder : LieAlgebra.derivedSeries K R 1 < ⊤ :=
    LieAlgebra.derivedSeries_lt_top_of_solvable K R
  have hDle : D ≤ R := LieSubmodule.lie_le_left R R
  refine lt_of_le_of_ne hDle ?_
  intro hEq
  change D = R at hEq
  have htop : LieAlgebra.derivedSeries K R 1 = ⊤ := by
    rw [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap]
    change D.comap R.incl = ⊤
    rw [hEq]
    exact LieIdeal.comap_incl_self R
  exact hder.ne htop

theorem levi_quotient_derived_radical_abelian
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] :
    let R := LieAlgebra.radical K L
    let D : LieIdeal K L := ⁅R, R⁆
    IsLieAbelian (LieAlgebra.radical K (L ⧸ D)) := by
  dsimp only
  let R := LieAlgebra.radical K L
  let D : LieIdeal K L := ⁅R, R⁆
  let q := leviQuotientMk D
  have hq : Function.Surjective q := leviQuotientMk_surjective D
  have hDle : D ≤ R := LieSubmodule.lie_le_left R R
  have hrad : R.map q = LieAlgebra.radical K (L ⧸ D) :=
    levi_radical_quotient D hDle
  rw [← hrad]
  refine ⟨?_⟩
  intro x y
  obtain ⟨rx, hrx⟩ := LieIdeal.mem_map_of_surjective hq x.2
  obtain ⟨ry, hry⟩ := LieIdeal.mem_map_of_surjective hq y.2
  apply Subtype.ext
  change ⁅x.1, y.1⁆ = 0
  rw [← hrx, ← hry, ← q.map_lie]
  have hbr : ⁅rx.1, ry.1⁆ ∈ D := LieSubmodule.lie_mem_lie rx.2 ry.2
  rw [← LieHom.mem_ker, leviQuotientMk_ker]
  exact hbr

theorem levi_decomposition_aux
    (n : ℕ) {K L : Type*} [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [Module.Finite K L]
    (hDim : Module.finrank K (LieAlgebra.radical K L) < n) :
    ∃ S : LieSubalgebra K L, LieAlgebra.IsSemisimple K S ∧
      ((LieAlgebra.radical K L : Submodule K L) + (S : Submodule K L) = ⊤) ∧
      ((LieAlgebra.radical K L : Submodule K L) ⊓ (S : Submodule K L) = ⊥) := by
  induction n generalizing L with
  | zero => omega
  | succ n ih =>
    let R := LieAlgebra.radical K L
    by_cases hRabelian : IsLieAbelian R
    · exact levi_exists_of_abelian_radical hRabelian
    · let D : LieIdeal K L := ⁅R, R⁆
      let q := leviQuotientMk D
      have hq : Function.Surjective q := leviQuotientMk_surjective D
      have hDle : D ≤ R := LieSubmodule.lie_le_left R R
      have hDlt : D < R := levi_derived_radical_lt hRabelian
      have hDfin : Module.finrank K D < Module.finrank K R :=
        Submodule.finrank_lt_finrank_of_lt hDlt
      have hQabelian : IsLieAbelian (LieAlgebra.radical K (L ⧸ D)) :=
        levi_quotient_derived_radical_abelian
      obtain ⟨T, hTsemi, hTsum, hTinf⟩ :=
        levi_exists_of_abelian_radical hQabelian
      let L₁ := T.comap q
      let qT := leviSubalgebraComapMap q T
      have hqT : Function.Surjective qT :=
        leviSubalgebraComapMap_surjective q hq T
      have _ : LieAlgebra.IsSemisimple K T := hTsemi
      have _ : LieAlgebra.IsSolvable q.ker := by
        rw [leviQuotientMk_ker]
        exact LieAlgebra.le_solvable_ideal_solvable hDle inferInstance
      have hRad₁ : LieAlgebra.radical K L₁ = qT.ker :=
        levi_radical_comap_semisimple q hq T
      have hFinKer : Module.finrank K qT.ker ≤ Module.finrank K q.ker :=
        LinearMap.finrank_le_finrank_of_injective
          (leviSubalgebraComapKerToKer_injective q T)
      have hFinRad₁ : Module.finrank K (LieAlgebra.radical K L₁) < n := by
        have hRle : Module.finrank K R ≤ n := Nat.lt_succ_iff.mp hDim
        have hkerD : Module.finrank K q.ker = Module.finrank K D := by
          rw [leviQuotientMk_ker]
        rw [hRad₁]
        calc
          Module.finrank K qT.ker ≤ Module.finrank K q.ker := hFinKer
          _ = Module.finrank K D := hkerD
          _ < Module.finrank K R := hDfin
          _ ≤ n := hRle
      obtain ⟨S₁, hS₁semi, hS₁sum, hS₁inf⟩ := ih hFinRad₁
      let S := S₁.map L₁.incl
      have hL₁incl : Function.Injective L₁.incl := by
        intro x y h
        exact Subtype.ext h
      let eS : S₁ ≃ₗ⁅K⁆ S :=
        LieSubalgebra.equivMapOfInjective L₁.incl S₁ hL₁incl
      let _ : LieAlgebra.IsSemisimple K S₁ := hS₁semi
      let _ : LieAlgebra.IsKilling K S₁ := inferInstance
      let _ : LieAlgebra.IsKilling K S := LieAlgebra.isKilling_of_equiv eS
      let _ : LieAlgebra.IsSemisimple K S := inferInstance
      have hRadQ : R.map q = LieAlgebra.radical K (L ⧸ D) :=
        levi_radical_quotient D hDle
      refine ⟨S, inferInstance, ?_, ?_⟩
      · rw [eq_top_iff]
        intro x _
        have hxQ : q x ∈
            (LieAlgebra.radical K (L ⧸ D) : Submodule K (L ⧸ D)) +
              (T : Submodule K (L ⧸ D)) := by
          rw [hTsum]
          trivial
        rw [Submodule.add_eq_sup, Submodule.mem_sup] at hxQ
        obtain ⟨a, ha, t, ht, hat⟩ := hxQ
        have haMap : a ∈ R.map q := by
          rw [hRadQ]
          exact ha
        obtain ⟨r, hr⟩ := LieIdeal.mem_map_of_surjective hq haMap
        have hxt : q (x - r.1) = t := by
          rw [map_sub, hr]
          rw [← hat]
          abel
        let l₁ : L₁ := ⟨x - r.1, by
          change q (x - r.1) ∈ T
          rw [hxt]
          exact ht⟩
        have hl₁Top : l₁ ∈
            (LieAlgebra.radical K L₁ : Submodule K L₁) +
              (S₁ : Submodule K L₁) := by
          rw [hS₁sum]
          trivial
        rw [Submodule.add_eq_sup, Submodule.mem_sup] at hl₁Top
        obtain ⟨z, hz, s, hs, hzs⟩ := hl₁Top
        have hzKer : z ∈ qT.ker := by
          rw [← hRad₁]
          exact hz
        have hzR : z.1 ∈ R := by
          have hzqT := LieHom.mem_ker.mp hzKer
          have hzq := congrArg Subtype.val hzqT
          change q z.1 = 0 at hzq
          have hzD : z.1 ∈ D := by
            rw [← leviQuotientMk_ker D, LieHom.mem_ker]
            exact hzq
          exact hDle hzD
        change x ∈ (R : Submodule K L) + (S : Submodule K L)
        rw [Submodule.add_eq_sup, Submodule.mem_sup]
        refine ⟨r.1 + z.1, R.add_mem r.2 hzR, s.1, ?_, ?_⟩
        · exact (LieSubalgebra.mem_map L₁.incl S₁ s.1).mpr ⟨s, hs, rfl⟩
        · have hl₁val : z.1 + s.1 = x - r.1 := congrArg Subtype.val hzs
          calc
            r.1 + z.1 + s.1 = r.1 + (z.1 + s.1) := by abel
            _ = r.1 + (x - r.1) := by rw [hl₁val]
            _ = x := by abel
      · rw [eq_bot_iff]
        intro x hx
        obtain ⟨s, hs, hsx⟩ := (LieSubalgebra.mem_map L₁.incl S₁ x).mp hx.2
        have hsR : s.1 ∈ R := by
          have hsval : s.1 = x := hsx
          rw [hsval]
          exact hx.1
        have hqsR : q s.1 ∈ LieAlgebra.radical K (L ⧸ D) := by
          rw [← hRadQ]
          exact LieIdeal.mem_map hsR
        have hqsT : q s.1 ∈ T := s.2
        have hqsBot : q s.1 ∈ (⊥ : Submodule K (L ⧸ D)) := by
          rw [← hTinf]
          exact ⟨hqsR, hqsT⟩
        have hqsZero : q s.1 = 0 := by simpa using hqsBot
        have hsKer : s ∈ qT.ker := by
          rw [LieHom.mem_ker]
          apply Subtype.ext
          exact hqsZero
        have hsRad : s ∈ LieAlgebra.radical K L₁ := by
          rw [hRad₁]
          exact hsKer
        have hsBot : s ∈ (⊥ : Submodule K L₁) := by
          rw [← hS₁inf]
          exact ⟨hsRad, hs⟩
        have hsZero : s = 0 := by simpa using hsBot
        change x = 0
        rw [← hsx, hsZero, map_zero]

/--
Every finite-dimensional Lie algebra `L` over a field `K` of characteristic zero decomposes as
`K`-vector spaces into its solvable radical `LieAlgebra.radical K L` plus a semisimple Levi factor
`S : LieSubalgebra K L` with sum `⊤` and intersection `⊥`. Source: E. E. Levi, Atti Accad. Sci.
Torino 1905 and A. I. Malcev, Izv. Akad. Nauk SSSR 1945; Bourbaki, Lie I; Lean states K-module
direct sum form over char-zero fields.

Proves `Wanted` entry `levi_decomposition`.

Proof: Weyl's complete reducibility theorem is proved with the trace-form Casimir operator. The
Levi factor is then constructed for an abelian radical and the general case follows by induction
through the derived ideal of the radical.
-/
theorem levi_decomposition
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] :
    ∃ (S : LieSubalgebra K L), LieAlgebra.IsSemisimple K S ∧
      (↑(LieAlgebra.radical K L) + (S : Submodule K L) = (⊤ : Submodule K L)) ∧
      (↑(LieAlgebra.radical K L) ⊓ (S : Submodule K L) = (⊥ : Submodule K L)) := by
  exact levi_decomposition_aux
    (Module.finrank K (LieAlgebra.radical K L) + 1) (Nat.lt_succ_self _)

end LeviDecomposition
