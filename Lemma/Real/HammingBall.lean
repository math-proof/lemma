import Mathlib
import sympy.Basic
import Def.InformationTheory.HammingBall
open scoped BigOperators
open Hamming


namespace Hamming

/--
[mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingBall.lean)
-/
@[path]
lemma mem_ball
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {x y : ι → F}
  {e : ℕ} :
-- imply
  y ∈ ball x e ↔ hammingDist x y ≤ e := by
-- proof
  simp [ball]

end Hamming

namespace Hamming

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
/--
[mem_supportFiber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingBall.lean)
-/
@[path]
private lemma mem_supportFiber {x y : ι → F} {s : Finset ι} :
  y ∈ supportFiber x s ↔ support x y = s := by
  simp only [supportFiber, Fintype.mem_piFinset, support, Finset.ext_iff,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h i
    specialize h i
    by_cases hi : i ∈ s
    · have hne : y i ≠ x i := by
      simpa only [ite_eq_left hi, Finset.mem_erase, Finset.mem_univ, and_true] using h
      exact ⟨fun _ ↦ hi, fun _ hxy ↦ hne hxy.symm⟩
    · have heq : y i = x i := by
      simpa only [ite_eq_right hi, Finset.mem_singleton] using h
      exact ⟨fun hxy ↦ (hxy heq.symm).elim, fun his ↦ (hi his).elim⟩
  · intro h i
    specialize h i
    by_cases hi : i ∈ s
    · rw [ite_eq_left hi, Finset.mem_erase]
      exact ⟨fun hyx ↦ h.mpr hi hyx.symm, Finset.mem_univ _⟩
    · rw [ite_eq_right hi, Finset.mem_singleton]
      exact (not_ne_iff.mp fun hxy ↦ hi (h.mp hxy)).symm

end Hamming

namespace Hamming

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
/--
[card_supportFiber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingBall.lean)
-/
@[path]
private lemma card_supportFiber (x : ι → F) (s : Finset ι) :
  (supportFiber x s).card = (Fintype.card F - 1) ^ s.card := by
  rw [supportFiber, Fintype.card_piFinset]
  simp only [apply_ite, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Finset.card_singleton]
  rw [Finset.prod_ite]
  simp [Finset.prod_const]

end Hamming

namespace Hamming

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
/--
[sphere_eq_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingBall.lean)
-/
@[path]
private lemma sphere_eq_biUnion (x : ι → F) (k : ℕ) :
  sphere x k = ((Finset.univ : Finset ι).powersetCard k).biUnion (supportFiber x) := by
  ext y
  simp only [sphere, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
    mem_supportFiber]
  constructor
  · intro hy
    refine ⟨support x y, ?_, rfl⟩
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, by simpa [hammingDist, support] using hy⟩
  · rintro ⟨s, hs, hsy⟩
    change (support x y).card = k
    rw [hsy]
    exact (Finset.mem_powersetCard.mp hs).2

end Hamming

namespace Hamming

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
/--
[card_sphere](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingBall.lean)
-/
@[path]
private lemma card_sphere (x : ι → F) (k : ℕ) :
  (sphere x k).card =
    (Fintype.card ι).choose k * (Fintype.card F - 1) ^ k := by
  rw [sphere_eq_biUnion, Finset.card_biUnion]
  · calc
    ∑ s ∈ (Finset.univ : Finset ι).powersetCard k, (supportFiber x s).card =
      ∑ _s ∈ (Finset.univ : Finset ι).powersetCard k,
        (Fintype.card F - 1) ^ k := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [card_supportFiber, (Finset.mem_powersetCard.mp hs).2]
    _ = ((Finset.univ : Finset ι).powersetCard k).card *
      (Fintype.card F - 1) ^ k := by simp
    _ = (Fintype.card ι).choose k * (Fintype.card F - 1) ^ k := by simp
  · intro s _ t _ hst
    change Disjoint (supportFiber x s) (supportFiber x t)
    rw [Finset.disjoint_left]
    intro y hys hyt
    apply hst
    rw [← mem_supportFiber.mp hys, ← mem_supportFiber.mp hyt]

end Hamming

namespace Hamming

/--
[card_ball](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingBall.lean)
-/
@[path]
lemma card_ball
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {x : ι → F}
  {e : ℕ} :
-- imply
  (ball x e).card =
    ∑ k ∈ Finset.range (e + 1),
    (Fintype.card ι).choose k * (Fintype.card F - 1) ^ k := by
-- proof
  unfold ball
  calc
    (Finset.univ.filter fun y => hammingDist x y ≤ e).card =
      ∑ k ∈ Finset.range (e + 1),
        ((Finset.univ.filter fun y => hammingDist x y ≤ e).filter fun y =>
          hammingDist x y = k).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro y hy
      exact Finset.mem_range.mpr (by
        have := (Finset.mem_filter.mp hy).2
        omega)
    _ = ∑ k ∈ Finset.range (e + 1), (sphere x k).card := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sphere]
      have hk' : k ≤ e := by
        have := Finset.mem_range.mp hk
        omega
      constructor
      · exact fun h => h.2
      · intro hy
        exact ⟨hy ▸ hk', hy⟩
    _ = ∑ k ∈ Finset.range (e + 1),
      (Fintype.card ι).choose k * (Fintype.card F - 1) ^ k := by simp

end Hamming

namespace Hamming

/--
[card_ball_fin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingBall.lean)
-/
@[path]
lemma card_ball_fin
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {n q : ℕ}
  {x : Fin n → F}
  {e : ℕ}
-- given
  (hn : 0 < n)
  (hq : Fintype.card F = q)
  (_hq₂ : 2 ≤ q) :
-- imply
  (ball x e).card = ∑ k ∈ Finset.range (e + 1), n.choose k * (q - 1) ^ k := by
-- proof
  simp [hq]

end Hamming


-- created on 2026-10-20
-- updated on 2026-10-23
