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
import Def.Combinatorics.DensityHalesJewett.Part11
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

theorem dhj_corollary11_blocks {k m₀ m : ℕ} {δ : ℝ}
    (hk : 2 ≤ k) (hm₀ : 0 < m₀) (hm₀m : m₀ ≤ m) (hkm : k ≤ m)
    (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hDHJ : dhjAt k m₀ (δ / 4))
    (hratio : ((k : ℝ) / (k + 1)) ^ m ≤ dhjEta k m₀ δ) :
    ∃ (G R : ℕ), 0 < G ∧
      ∀ A : Finset (Fin (R + 1) → Fin G → Fin (k + 1)),
        δ ≤ dhjDensity A →
        dhjLineFree
          (A.map (dhjFlattenEquiv (L := R + 1) (G := G)
            (α := Fin (k + 1))).toEmbedding) →
        ∃ (W : Combinatorics.Subspace (Fin m) (Fin (k + 1))
              (Fin (R + 1) × Fin G))
          (D : Fin k → Finset (Fin m → Fin (k + 1))),
          (∀ i, dhjInsensitive i (D i)) ∧
          dhjGamma k m₀ δ ≤ dhjDensity (dhjFamilyMeet D) ∧
          (δ + dhjGamma k m₀ δ) * dhjDensity (dhjFamilyMeet D) ≤
            dhjDensity (dhjPullback W
              (A.map (dhjFlattenEquiv (L := R + 1) (G := G)
                (α := Fin (k + 1))).toEmbedding) ∩ dhjFamilyMeet D) := by
  classical
  obtain ⟨hθpos, hθle, hηpos, hηlt, hηsq, hγpos, hγle⟩ :=
    dhj_constants hk hm₀ hδ hδle
  obtain ⟨G, R, hG, hregular⟩ :=
    dhj_lemma7_blocks (by omega) hm₀ hm₀m hδ
      (by positivity : 0 < dhjEta k m₀ δ ^ 2 / 2)
      hηsq hDHJ
  refine ⟨G, R, hG, ?_⟩
  intro A hA hlineFree
  obtain ⟨t, ht, p, V, hsections, hlines⟩ := hregular A hA
  obtain hhigh | hlow := dhj_lemma8_blocks (by omega) (hm₀.trans_le hm₀m)
    hηpos hθpos hηlt ht A p V hsections hlines
  · obtain ⟨y, hy⟩ := hhigh
    let W := dhjBlockFullSubspace p (dhjSubspaceMapConstants Fin.castSucc V) y
      (by omega : t + 1 ≤ R + 1)
    let B := dhjColumn
      (fun x : Fin m → Fin (k + 1) => dhjBlockSection A
        (dhjAppend p (dhjSubspaceMapConstants Fin.castSucc V x)) (by omega)) y
    let D : Fin k → Finset (Fin m → Fin (k + 1)) := fun _ => Finset.univ
    have hpull : dhjPullback W
        (A.map (dhjFlattenEquiv (L := R + 1) (G := G)
          (α := Fin (k + 1))).toEmbedding) = B := by
      exact dhjPullback_blockFullSubspace A p
        (dhjSubspaceMapConstants Fin.castSucc V) y (by omega)
    have hmeet : dhjFamilyMeet D = Finset.univ := dhj_familyMeet_univ
    refine ⟨W, D, ?_, ?_, ?_⟩
    · intro i
      exact dhjInsensitive_univ i
    · rw [hmeet, dhjDensity_univ]
      exact hγle.trans (hηsq.trans (by linarith))
    · rw [hmeet, dhjDensity_univ, mul_one, Finset.inter_univ, hpull]
      calc
        δ + dhjGamma k m₀ δ ≤ δ + dhjEta k m₀ δ ^ 2 / 2 :=
          by linarith
        _ ≤ dhjDensity B := by simpa [B] using hy
  · obtain ⟨y, hyden, hygood⟩ := hlow
    let W := dhjBlockFullSubspace p (dhjSubspaceMapConstants Fin.castSucc V) y
      (by omega : t + 1 ≤ R + 1)
    let B := dhjColumn
      (fun x : Fin m → Fin (k + 1) => dhjBlockSection A
        (dhjAppend p (dhjSubspaceMapConstants Fin.castSucc V x)) (by omega)) y
    have hpull : dhjPullback W
        (A.map (dhjFlattenEquiv (L := R + 1) (G := G)
          (α := Fin (k + 1))).toEmbedding) = B := by
      exact dhjPullback_blockFullSubspace A p
        (dhjSubspaceMapConstants Fin.castSucc V) y (by omega)
    have hBlineFree : dhjLineFree B := by
      rw [← hpull]
      exact dhjLineFree_pullback _ W hlineFree
    have hgood : dhjTheta k m₀ δ / 2 ≤ dhjDensity (dhjGoodRestrictedLines B) := by
      rw [← dhj_column_lineEvents_eq_goodLines A p V y ht]
      exact hygood
    obtain ⟨D, hDi, hDmass, hDcorr⟩ :=
      dhj_corollary11_cube (by omega) hkm hδ hδle hθpos hθle rfl rfl hratio B
        hBlineFree hyden hgood
    refine ⟨W, D, hDi, hDmass, ?_⟩
    rwa [hpull]

end MathlibExt.Combinatorics.DensityHalesJewettWanted
