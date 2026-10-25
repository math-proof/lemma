/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Combinatorics.HalesJewett
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Def.Combinatorics.DensityHalesJewett.Part14
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

theorem dhj_exists_family_tiling {k d : ℕ} {β : ℝ}
    (hk : 2 ≤ k) (hd : 0 < d) (hβ : 0 < β) (hβle : β ≤ 1)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε) :
    ∃ n : ℕ, ∀ (D : Fin k → Finset (Fin n → Fin (k + 1))),
      (∀ i, dhjInsensitive i (D i)) →
        ∃ C : Finset (Fin n → Fin (k + 1)),
          C ⊆ dhjFamilyMeet D ∧ dhjTiled d k C ∧
            dhjDensity (dhjFamilyMeet D \ C) ≤ 2 * (k : ℝ) * β := by
  obtain ⟨n, hn⟩ := dhj_exists_structured_tiling hk hDHJ k d hd β hβ hβle
  refine ⟨n, ?_⟩
  intro D hD
  obtain ⟨C, hCsub, hCtile, hCsmall⟩ := hn (fun i => i) D hD
  rw [dhjMeet_eq_familyMeet] at hCsub hCsmall
  exact ⟨C, hCsub, hCtile, hCsmall⟩

theorem dhj_dichotomy_blocks {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 →
      ∀ d : ℕ, 0 < d → ∃ G R : ℕ, 0 < G ∧
      ∀ A : Finset (Fin (R + 1) → Fin G → Fin (k + 1)),
        ρ ≤ dhjDensity A →
          let A' := A.map (dhjFlattenEquiv (L := R + 1) (G := G)
            (α := Fin (k + 1))).toEmbedding
          (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin (R + 1) × Fin G),
              dhjLineIn A' l) ∨
            ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1))
                (Fin (R + 1) × Fin G),
              ρ + γ / 2 ≤ dhjDensityOn A' V := by
  classical
  obtain ⟨N₀, hN₀⟩ := hDHJ (δ / 4) (by positivity)
  let m₀ := N₀ + 1
  have hm₀ : 0 < m₀ := by simp [m₀]
  have hAt : dhjAt k m₀ (δ / 4) := hN₀ m₀ (by simp [m₀])
  obtain ⟨hθpos, hθle, hηpos, hηlt, hηsq, hγpos, hγle⟩ :=
    dhj_constants hk hm₀ hδ hδle
  let γ := dhjGamma k m₀ δ
  let η := dhjEta k m₀ δ
  have hηleone : η ≤ 1 := by
    dsimp only [η]
    linarith
  have hηsqle : η ^ 2 ≤ η := by
    nlinarith [mul_nonneg hηpos.le (sub_nonneg.mpr hηleone)]
  have hγleone : γ ≤ 1 := by
    dsimp only [γ, η] at hγle ⊢
    nlinarith
  have hγsqhalf_lt_one : γ ^ 2 / 2 < 1 := by
    nlinarith [mul_nonneg hγpos.le (sub_nonneg.mpr hγleone)]
  have hγsqhalf_lt_gamma : γ ^ 2 / 2 < γ := by
    nlinarith [mul_nonneg hγpos.le (sub_nonneg.mpr hγleone)]
  let β := γ ^ 2 / (4 * (k : ℝ))
  have hβpos : 0 < β := by dsimp only [β]; positivity
  have hβle : β ≤ 1 := by
    dsimp only [β]
    rw [div_le_one (by positivity : (0 : ℝ) < 4 * k)]
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [sq_nonneg γ,
      mul_nonneg hγpos.le (sub_nonneg.mpr hγleone)]
  have herr : 2 * (k : ℝ) * β = γ ^ 2 / 2 := by
    dsimp only [β]
    field_simp
    ring
  refine ⟨γ, hγpos, ?_⟩
  intro ρ hδρ hρle
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hAtρ : dhjAt k m₀ (ρ / 4) := by
    intro A hA
    exact hAt A (by linarith)
  obtain ⟨hθρpos, hθρle, hηρpos, hηρlt, hηρsq, hγρpos, hγρle⟩ :=
    dhj_constants hk hm₀ hρ hρle
  let ηρ := dhjEta k m₀ ρ
  let γρ := dhjGamma k m₀ ρ
  have hθmono : dhjTheta k m₀ δ ≤ dhjTheta k m₀ ρ := by
    simp only [dhjTheta]
    gcongr
  have hηmono : η ≤ ηρ := by
    simp only [η, ηρ, dhjEta]
    gcongr
  have hγmono : γ ≤ γρ := by
    simp only [γ, γρ, dhjGamma]
    gcongr
  have hηρleone : ηρ ≤ 1 := by
    dsimp only [ηρ]
    linarith
  have hηρsqle : ηρ ^ 2 ≤ ηρ := by
    nlinarith [mul_nonneg hηρpos.le (sub_nonneg.mpr hηρleone)]
  have hγρleone : γρ ≤ 1 := by
    dsimp only [γρ, ηρ] at hγρle ⊢
    nlinarith
  have hγρsqhalf_lt : γρ ^ 2 / 2 < γρ := by
    nlinarith [mul_nonneg hγρpos.le (sub_nonneg.mpr hγρleone)]
  intro d hd
  obtain ⟨M₀, hkM₀, hratio⟩ :=
    dhj_exists_ratio_pow_le (by omega : 0 < k) hηpos
  let d' := max d (max M₀ m₀)
  have hd' : 0 < d' := hd.trans_le (le_max_left _ _)
  obtain ⟨m, hTile⟩ :=
    dhj_exists_family_tiling hk hd' hβpos hβle hDHJ
  let Dall : Fin k → Finset (Fin m → Fin (k + 1)) := fun _ => Finset.univ
  have hDall : ∀ i, dhjInsensitive i (Dall i) := fun i => dhjInsensitive_univ i
  obtain ⟨Call, hCallSub, hCallTile, hCallSmall⟩ := hTile Dall hDall
  have hmeetAll : dhjFamilyMeet Dall = Finset.univ := dhj_familyMeet_univ
  have hCallSmall' : dhjDensity (Finset.univ \ Call) ≤ γ ^ 2 / 2 := by
    rw [← herr, ← hmeetAll]
    exact hCallSmall
  have hCallNe : Call.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sdiff_empty,
      dhjDensity_univ] at hCallSmall'
    linarith
  have hd'm : d' ≤ m := hCallTile.dimension_le_of_nonempty hCallNe
  have hm₀m : m₀ ≤ m := by
    apply (le_max_right M₀ m₀).trans
    exact (le_max_right d (max M₀ m₀)).trans hd'm
  have hM₀m : M₀ ≤ m := by
    apply (le_max_left M₀ m₀).trans
    exact (le_max_right d (max M₀ m₀)).trans hd'm
  have hkm : k ≤ m := hkM₀.trans hM₀m
  have hratioM : ((k : ℝ) / (k + 1)) ^ m ≤ dhjEta k m₀ ρ :=
    (hratio m hM₀m).trans hηmono
  obtain ⟨G, R, hG, hCorr⟩ :=
    dhj_corollary11_blocks hk hm₀ hm₀m hkm hρ hρle hAtρ hratioM
  refine ⟨G, R, hG, ?_⟩
  intro A hA
  let A' := A.map (dhjFlattenEquiv (L := R + 1) (G := G)
    (α := Fin (k + 1))).toEmbedding
  by_cases hlineFree : dhjLineFree A'
  · right
    obtain ⟨W, D, hDi, hDmass, hDcorr⟩ := hCorr A hA hlineFree
    obtain ⟨C, hCsub, hCtile, hCsmall⟩ := hTile D hDi
    have hCsmall' : dhjDensity (dhjFamilyMeet D \ C) ≤ γ ^ 2 / 2 := by
      rw [← herr]
      exact hCsmall
    have hCsmallρ : dhjDensity (dhjFamilyMeet D \ C) ≤ γρ ^ 2 / 2 := by
      calc
        dhjDensity (dhjFamilyMeet D \ C) ≤ γ ^ 2 / 2 := hCsmall'
        _ ≤ γρ ^ 2 / 2 := by
          exact div_le_div_of_nonneg_right
            ((sq_le_sq₀ hγpos.le hγρpos.le).2 hγmono) (by norm_num)
    let B := dhjPullback W A'
    have hCcorr : (ρ + γρ / 2) * dhjDensity C ≤ dhjDensity (B ∩ C) := by
      exact dhj_correlation_after_tiling hρ hγρpos hCsub hDmass hCsmallρ hDcorr
    have hCne : C.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sdiff_empty] at hCsmallρ
      exact (not_le_of_gt hγρsqhalf_lt) (hDmass.trans hCsmallρ)
    obtain ⟨V, hVsub, hVden⟩ :=
      hCtile.exists_densityOn_ge B hCne hCcorr
    let Z := W.comp V
    have hd_d' : d ≤ d' := le_max_left d (max M₀ m₀)
    obtain ⟨U, hUden⟩ :=
      dhj_exists_subspace_density_ge hd_d' (dhjPullback Z A')
    refine ⟨Z.comp U, ?_⟩
    calc
      ρ + γ / 2 ≤ ρ + γρ / 2 := by linarith
      _ ≤ dhjDensityOn B V := hVden
      _ = dhjDensityOn A' Z := (dhjDensityOn_comp A' W V).symm
      _ = dhjDensity (dhjPullback Z A') := rfl
      _ ≤ dhjDensityOn (dhjPullback Z A') U := hUden
      _ = dhjDensityOn A' (Z.comp U) := (dhjDensityOn_comp A' Z U).symm
  · left
    simpa only [dhjLineFree, not_forall, Classical.not_not] using hlineFree

theorem dhj_dichotomy_fin {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 →
      ∀ d : ℕ, 0 < d → ∃ N : ℕ, 0 < N ∧
      ∀ A : Finset (Fin N → Fin (k + 1)), ρ ≤ dhjDensity A →
        (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin N), dhjLineIn A l) ∨
          ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin N),
            ρ + γ / 2 ≤ dhjDensityOn A V := by
  classical
  obtain ⟨γ, hγ, hblocks⟩ := dhj_dichotomy_blocks hk hδ hδle hDHJ
  refine ⟨γ, hγ, ?_⟩
  intro ρ hδρ hρle d hd
  obtain ⟨G, R, hG, hblock⟩ := hblocks ρ hδρ hρle d hd
  let I := Fin (R + 1) × Fin G
  let N := Fintype.card I
  let e : I ≃ Fin N := Fintype.equivFin I
  let b := dhjFlattenEquiv (L := R + 1) (G := G) (α := Fin (k + 1))
  let w := dhjWordEquiv e ( α := Fin (k + 1))
  let f := b.trans w
  have hN : 0 < N := by
    apply Fintype.card_pos_iff.mpr
    let q : I := (⟨0, by omega⟩, ⟨0, hG⟩)
    exact ⟨q⟩
  refine ⟨N, hN, ?_⟩
  intro A hA
  let Ablock := A.map f.symm.toEmbedding
  have hAblock : ρ ≤ dhjDensity Ablock := by
    rw [dhjDensity_map_equiv]
    exact hA
  obtain hline | hinc := hblock Ablock hAblock
  · left
    obtain ⟨l, hl⟩ := hline
    refine ⟨l.reindex e, ?_⟩
    intro a
    have ha := hl a
    change l a ∈ Ablock.map b.toEmbedding at ha
    rw [dhj_mem_map_equiv] at ha
    dsimp only [Ablock] at ha
    rw [dhj_mem_map_equiv] at ha
    have heq : l.reindex e a = w (l a) := by
      funext q
      change l.reindex e a q = l a (e.symm q)
      exact Combinatorics.Line.reindex_apply l e a q
    rw [heq]
    simpa [f] using ha
  · right
    obtain ⟨V, hV⟩ := hinc
    let V' := V.reindex (Equiv.refl (Fin d))
      (Equiv.refl (Fin (k + 1))) e
    refine ⟨V', ?_⟩
    have hpull : dhjPullback V' A = dhjPullback V
        (Ablock.map b.toEmbedding) := by
      ext z
      simp only [dhj_mem_pullback]
      rw [dhj_mem_map_equiv]
      dsimp only [Ablock]
      rw [dhj_mem_map_equiv]
      change V' z ∈ A ↔ f (b.symm (V z)) ∈ A
      have hVapply : V' z = w (V z) := dhjSubspace_reindex_apply V e z
      rw [hVapply]
      rfl
    simpa [dhjDensityOn, hpull] using hV

theorem dhjThreshold_succ {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε)
    {δ : ℝ} (hδ : 0 < δ) : dhjThreshold (k + 1) δ := by
  by_cases hδle : δ ≤ 1
  · obtain ⟨γ, hγ, hstep⟩ := dhj_dichotomy_fin hk hδ hδle hDHJ
    obtain ⟨r, hr⟩ := exists_nat_gt ((1 - δ) / (γ / 2))
    have hinc : 0 < γ / 2 := by positivity
    have htop : 1 < δ + (r : ℝ) * (γ / 2) := by
      have hmul := mul_lt_mul_of_pos_right hr hinc
      rw [div_mul_cancel₀ (1 - δ) hinc.ne'] at hmul
      linarith
    obtain ⟨N, hN, hAt⟩ :=
      dhj_iterate_dichotomy hδ hγ hstep r δ le_rfl htop
    exact dhjThreshold_of_at (by omega) hAt
  · refine ⟨1, ?_⟩
    intro n hn A hA
    have hAle : dhjDensity A ≤ 1 := dhjDensity_le_one A
    exfalso
    exact (not_le_of_gt (lt_of_not_ge hδle)) (hA.trans hAle)

theorem dhjThreshold_add_two : ∀ t : ℕ, ∀ δ : ℝ, 0 < δ →
    dhjThreshold (t + 2) δ := by
  intro t
  induction t with
  | zero =>
      intro δ hδ
      simpa using dhjThreshold_two hδ
  | succ t ih =>
      intro δ hδ
      have h := dhjThreshold_succ (k := t + 2) (by omega)
        (fun ε hε => ih ε hε) hδ
      exact h

theorem dhjThreshold_all (k : ℕ) (hk : 2 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    dhjThreshold k δ := by
  have h := dhjThreshold_add_two (k - 2) δ hδ
  convert h using 1
  omega

/--
For every `k ≥ 2` and `δ > 0` there is `N` such that every `A : Finset (Fin N → Fin k)` with `δ *
((k : ℝ) ^ N) ≤ (A.card : ℝ)` contains a combinatorial line `l : Combinatorics.Line (Fin k) (Fin
N)` with `l a ∈ A` for all `a`. Source: H. Furstenberg and Y. Katznelson, J. Anal. Math. 57 (1991)
and Hales-Jewett, Trans. AMS 106 (1963); Lean states finitary density form over `Fin N → Fin k`
with coloring version as corollary.

Proves `Wanted` entry `density_hales_jewett`.

Proof: We follow the density-increment route of Dodos–Kanellopoulos–Tyros, with the binary
case supplied by Sperner's theorem and the required Graham–Rothschild line theorem proved above.
-/
theorem density_hales_jewett :
    ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ,
      ∀ A : Finset (Fin N → Fin k),
        δ * ((k : ℝ) ^ N) ≤ (A.card : ℝ) →
          ∃ l : Combinatorics.Line (Fin k) (Fin N), ∀ a : Fin k, l a ∈ A := by
  intro k hk δ hδ
  obtain ⟨N, hN⟩ := dhjThreshold_all k hk δ hδ
  refine ⟨N, ?_⟩
  intro A hA
  have hden : δ ≤ dhjDensity A := by
    rw [dhjDensity]
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    rw [le_div_iff₀ (by positivity)]
    exact hA
  obtain ⟨l, hl⟩ := hN N le_rfl A hden
  exact ⟨l, hl⟩

end MathlibExt.Combinatorics.DensityHalesJewettWanted
