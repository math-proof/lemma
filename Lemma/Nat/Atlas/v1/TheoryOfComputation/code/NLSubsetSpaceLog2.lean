import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.LogSpace
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.LogSpace
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.SpaceComplexity
open SpaceComplexity


namespace LogSpace

/--
[savitch_log](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NLSubsetSpaceLog2.lean)
-/
@[path]
lemma savitch_log
  {Γ : Type}
  {A : Set (List Γ)}
-- given
  (hA : InNSPACE log A) :
-- imply
  InSPACE (fun n => (log n) ^ 2) A := by
-- proof
  obtain ⟨Q, hFin, hDec, N, hLang, g, hAsymp, hSpace⟩ := hA
  haveI := hFin
  haveI := hDec
  have hLang_cond : ∀ w ∈ N.language, ∀ s ∈ w, s ∈ N.inputAlpha := by
    intro w hw s hs
    exact hw.1 s hs
  obtain ⟨Q', hFin', hDec', M, hMLang, g', hg'bound, hMSpace⟩ :=
    SpaceComplexity.dtm_of_nspace_bounded N g hSpace hLang_cond
  refine ⟨Q', hFin', hDec', M, ?_, g', ?_, hMSpace⟩
  · exact hMLang.trans hLang
  · obtain ⟨c, n₀, hc, hbnd⟩ := hAsymp
    refine ⟨c ^ 2, n₀, by positivity, fun n hn => ?_⟩
    calc g' n ≤ (g n) ^ 2 := hg'bound n
      _ ≤ (c * log n) ^ 2 := Nat.pow_le_pow_left (hbnd n hn) 2
      _ = c ^ 2 * (log n) ^ 2 := Nat.mul_pow c (log n) 2

end LogSpace

namespace LogSpace

/--
[nl_subset_space_log2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NLSubsetSpaceLog2.lean)
-/
@[path]
lemma nl_subset_space_log2
  {Γ : Type}
  {A : Set (List Γ)} :
-- imply
  InNL A → InSPACE (fun n => (log n) ^ 2) A := by
-- proof
  intro hA
  unfold InNL at hA
  exact savitch_log A hA

end LogSpace


-- created on 2026-10-23
