import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6
open LovaszLocalLemma Beck
open Set Finset
open Set Topology Finset


namespace LovaszLocalLemma

/--
[isClopen_eval_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6.lean)
-/
@[path]
lemma isClopen_eval_eq
  {k : ℕ}
  {x : ℝ}
  {i : Fin k} :
-- imply
  IsClopen {c : ℝ → Fin k | c x = i} := by
-- proof
  have heq : {c : ℝ → Fin k | c x = i} = (fun c => c x) ⁻¹' {i} := by
    ext c; simp
  rw [heq]
  exact ⟨(isClosed_discrete _).preimage (continuous_apply x),
    (isOpen_discrete _).preimage (continuous_apply x)⟩

end LovaszLocalLemma

namespace LovaszLocalLemma

/--
[isClosed_goodColorings](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6.lean)
-/
@[path]
lemma isClosed_goodColorings
  {k : ℕ}
  {S : Finset ℝ}
  {t : ℝ}
-- given
  (_hk : 0 < k) :
-- imply
  IsClosed (goodColorings k S t) := by
-- proof
  suffices h : goodColorings k S t =
    ⋂ (i : Fin k), ⋃ s ∈ S, {c : ℝ → Fin k | c (↑s + t) = i} by
    rw [h]
    apply isClosed_iInter
    intro i
    exact S.finite_toSet.isClosed_biUnion (fun s _ =>
      (isClopen_eval_eq (↑s + t) i).1)
  ext c
  simp only [goodColorings, IsMulticolored, translate, Set.mem_setOf_eq, Set.mem_image,
    Set.mem_iInter, Set.mem_iUnion, Finset.mem_coe]
  constructor
  · intro h i
    obtain ⟨x, ⟨s, hs, hsx⟩, hc⟩ := h i
    exact ⟨s, hs, hsx ▸ hc⟩
  · intro h i
    obtain ⟨s, hs, hc⟩ := h i
    exact ⟨s + t, ⟨s, hs, rfl⟩, hc⟩
/-- Empty.Finite-translate version (proved via the symmetric LLL): under the size condition $e \cdot (m(m-1) + 1) \cdot k \cdot (1 - 1/k)^m \le 1$, for any finite set of shifts $T$ there is a $k$-coloring of $\mathbb{R}$ that is multicolored on every translate $S + t$, $t \in T$. -/
end LovaszLocalLemma
noncomputable section
namespace Beck
open Set Topology Finset


namespace Beck

/--
[isOpen_monochromaticAP](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6.lean)
-/
@[path]
lemma isOpen_monochromaticAP
  {k : ℕ}
  {a d : ℤ} :
-- imply
  IsOpen {c : ℤ → Bool | IsMonochromaticAP c k a d} := by
-- proof
  simp only [IsMonochromaticAP, setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  have h : {c : ℤ → Bool | c (a + ↑(i : ℕ) * d) = c a} =
    (fun c => (c (a + ↑(i : ℕ) * d), c a)) ⁻¹' {p : Bool × Bool | p.1 = p.2} := by
    ext c; simp
  rw [h]
  exact ((continuous_apply _).prodMk (continuous_apply _)).isOpen_preimage _ (isOpen_discrete _)
/-- Empty.Finite version of Beck's theorem on monochromatic APs: for any $\varepsilon > 0$ there is a threshold $k_0$ such that any finite list of AP constraints $(k, a, d)$ with $k \ge k_0$ and $0 < d < 2^{(1-\varepsilon) k}$ can be simultaneously broken by some $\{0,1\}$-coloring of $\mathbb{Z}$. -/

end Beck


-- created on 2026-10-23
