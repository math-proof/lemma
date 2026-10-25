import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.PosOfAscentProof
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.WordSigmaInvariance
import Def.v1.Atlas.Buildings.code.CoxeterGroup.RootSystem
import Def.v1.Atlas.Buildings.code.CoxeterGroup.Reflections
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterHomomorphism.Part2
import Lemma.List.WordSigma.eq.AddMulS_WordSigma_E.of.All_Eq_0.Ne
import Lemma.List.EqWordSSigma.of.WordProd
import Lemma.Real.IsRoot_Sigma
import Lemma.List.IsReducedDrop.of.IsReduced
import Lemma.List.Eq_E.of.IsPositive_IsNegativeSigma_EqBilinForm
open Finset BigOperators List CoxeterGroup Real


namespace CoxeterGroup

/--
[e_not_isNegative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignChangeExchangeFinal.lean)
-/
@[path]
private lemma e_not_isNegative
  [DecidableEq B]
  [Fintype B]
  {s : B} :
-- imply
  ¬ IsNegative (e s) := by
-- proof
  intro h
  have hs := h s
  simp [e] at hs
  linarith

end CoxeterGroup

namespace CoxeterGroup

/--
[coxeterRepresentation_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignChangeExchangeFinal.lean)
-/
@[path]
private lemma coxeterRepresentation_injective
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W} :
-- imply
  Function.Injective (coxeterRepresentation M cs) := by
-- proof
  intro g₁ g₂ hρ
  suffices h : g₁ * g₂⁻¹ = 1 by
    have := congrArg (fun x => x * g₂) h
    simpa [mul_assoc, inv_mul_cancel] using this
  by_contra hw_ne
  have hρw : coxeterRepresentation M cs (g₁ * g₂⁻¹) = 1 := by
    rw [map_mul, map_inv, hρ, mul_inv_cancel]
  have hlen_pos : 0 < cs.length (g₁ * g₂⁻¹) := by
    rwa [Nat.pos_iff_ne_zero, ne_eq, cs.length_eq_zero_iff]
  obtain ⟨word, hred_word, hprod_word⟩ := cs.exists_isReduced (g₁ * g₂⁻¹)
  have hred : cs.IsReduced word := hred_word
  have hword_ne : word ≠ [] := by
    intro h
    subst h
    simp [CoxeterSystem.wordProd_nil] at hprod_word
    exact hw_ne hprod_word
  have hword_len : 0 < word.length := by
    rwa [← hred, ← hprod_word]
  set sₙ := word.getLast hword_ne
  have hid : ∀ v, wordSigma M word v = v := by
    intro v
    have h1 := coxeterRepresentation_wordProd_apply M cs word v
    have h2 : coxeterRepresentation M cs (cs.wordProd word) = 1 := by
      rwa [← hprod_word]
    rw [h2] at h1
    simpa [LinearEquiv.coe_one] using h1.symm
  have hdesc_sn : cs.length (cs.wordProd word * cs.simple sₙ) <
      cs.length (cs.wordProd word) := by
    have hprod' : cs.wordProd word = cs.wordProd word.dropLast * cs.simple sₙ := by
      conv_lhs => rw [← List.dropLast_append_getLast hword_ne]
      rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton]
    have : cs.wordProd word * cs.simple sₙ = cs.wordProd word.dropLast := by
      rw [hprod', mul_assoc, cs.simple_mul_simple_self, mul_one]
    rw [this]
    have hlen_drop : cs.length (cs.wordProd word.dropLast) ≤ word.dropLast.length :=
      cs.length_wordProd_le _
    have hlen_lt : word.dropLast.length < word.length := by
      rw [List.length_dropLast]
      exact Nat.sub_one_lt_of_le hword_len le_rfl
    have hlen_eq : word.length = cs.length (cs.wordProd word) := hred.symm
    omega
  have hneg_sn : IsNegative (wordSigma M word (e sₙ)) :=
    neg_of_descent M cs word sₙ hred hdesc_sn
  rw [hid (e sₙ)] at hneg_sn
  exact e_not_isNegative (s := sₙ) hneg_sn

end CoxeterGroup

namespace CoxeterGroup

/--
[wordProd_cons_eq_append_of_wordSigma_eq_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignChangeExchangeFinal.lean)
-/
@[path]
private lemma wordProd_cons_eq_append_of_wordSigma_eq_e
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {tail : List B}
  {s t : B}
-- given
  (hsigma : wordSigma M tail (e s) = e t) :
-- imply
  cs.simple t * cs.wordProd tail = cs.wordProd tail * cs.simple s := by
-- proof
  apply coxeterRepresentation_injective (M := M) (cs := cs)
  ext v
  have lhs_eq : (coxeterRepresentation M cs (cs.simple t * cs.wordProd tail)) v =
      sigma M t (wordSigma M tail v) := by
    simp only [map_mul, LinearEquiv.mul_apply, coxeterRepresentation_simple,
      sigmaLinearEquiv_apply, coxeterRepresentation_wordProd_apply]
  have rhs_eq : (coxeterRepresentation M cs (cs.wordProd tail * cs.simple s)) v =
      wordSigma M tail (sigma M s v) := by
    simp only [map_mul, LinearEquiv.mul_apply, coxeterRepresentation_simple,
      sigmaLinearEquiv_apply, coxeterRepresentation_wordProd_apply]
  rw [lhs_eq, rhs_eq]
  have hB : bilinForm M (wordSigma M tail v) (e t) = bilinForm M v (e s) := by
    rw [← hsigma, wordSigma_preserves_form]
  have hlin_add : ∀ (w : List B) (a b : B → ℝ),
      wordSigma M w (a + b) = wordSigma M w a + wordSigma M w b := by
    intro w a b
    have h1 := coxeterRepresentation_wordProd_apply M cs w (a + b)
    have h2 := coxeterRepresentation_wordProd_apply M cs w a
    have h3 := coxeterRepresentation_wordProd_apply M cs w b
    rw [← h1, ← h2, ← h3]
    simp [map_add]
  have hlin_smul : ∀ (w : List B) (c : ℝ) (a : B → ℝ),
      wordSigma M w (c • a) = c • wordSigma M w a := by
    intro w c a
    have h1 := coxeterRepresentation_wordProd_apply M cs w (c • a)
    have h2 := coxeterRepresentation_wordProd_apply M cs w a
    rw [← h1, ← h2]
    simp [map_smul]
  have hsigma_eq : sigma M s v = v + (-2 * bilinForm M v (e s)) • e s := by
    ext u
    simp [sigma, Pi.add_apply, Pi.smul_apply]
    ring
  have hrhs : wordSigma M tail (sigma M s v) =
      wordSigma M tail v + (-2 * bilinForm M v (e s)) • e t := by
    rw [hsigma_eq, hlin_add, hlin_smul, hsigma]
  have hlhs : sigma M t (wordSigma M tail v) =
      wordSigma M tail v + (-2 * bilinForm M (wordSigma M tail v) (e t)) • e t := by
    ext u
    simp [sigma, Pi.add_apply, Pi.smul_apply]
    ring
  rw [hlhs, hrhs, hB]

end CoxeterGroup

namespace CoxeterGroup

/--
[wordSigma_reflection_root_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ReflectionLengthDecrease.lean)
-/
@[path]
private lemma wordSigma_reflection_root_neg
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word_u : List B}
  {j : B} :
-- imply
  let α := wordSigma M word_u (e j)
  let u := cs.wordProd word_u
  let t := u * cs.simple j * u⁻¹
  ∀ word_t : List B, cs.wordProd word_t = t → ∀ v : B → ℝ,
    wordSigma M word_t v = generalizedReflection M α v := by
-- proof
  intro α u t word_t hprod_t v
  obtain ⟨word_u_inv, _, hprod_inv⟩ := cs.exists_isReduced (cs.wordProd word_u)⁻¹
  have hprod_concat : cs.wordProd (word_u ++ [j] ++ word_u_inv) = t := by
    rw [cs.wordProd_append, cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil,
      mul_one, ← hprod_inv]
  have hsame : wordSigma M word_t v = wordSigma M (word_u ++ [j] ++ word_u_inv) v :=
    wordSigma_eq_of_wordProd_eq M cs word_t (word_u ++ [j] ++ word_u_inv)
      (by rw [hprod_t, hprod_concat]) v
  rw [hsame]
  rw [List.append_assoc, wordSigma_append, wordSigma_append, wordSigma_singleton]
  set v' := wordSigma M word_u_inv v with hv'_def
  have hcancel : wordSigma M word_u (wordSigma M word_u_inv v) = v := by
    have hprod_id : cs.wordProd (word_u ++ word_u_inv) = 1 := by
      rw [cs.wordProd_append, ← hprod_inv, mul_inv_cancel]
    have heq := wordSigma_eq_of_wordProd_eq M cs (word_u ++ word_u_inv) []
      (by rw [hprod_id, cs.wordProd_nil]) v
    rwa [wordSigma_append] at heq
  have hsigma_eq : sigma M j v' = v' + (-2 * bilinForm M v' (e j)) • (e j) := by
    ext t
    simp only [sigma, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsigma_eq, wordSigma_add, wordSigma_smul, hcancel]
  have hform : bilinForm M v' (e j) = bilinForm M v α := by
    rw [hv'_def, ← wordSigma_preserves_form M word_u (wordSigma M word_u_inv v) (e j),
      hcancel]
  rw [hform]
  change v + (-2 * bilinForm M v α) • α = generalizedReflection M α v
  ext x
  simp only [generalizedReflection, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end CoxeterGroup

namespace CoxeterGroup

/--
[conjugate_reflection_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ReflectionLengthDecrease.lean)
-/
@[path]
private lemma conjugate_reflection_eq
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word_u : List B}
  {j : B} :
-- imply
  let α := wordSigma M word_u (e j)
  let u := cs.wordProd word_u
  let t := u * cs.simple j * u⁻¹
  ∀ word_t : List B, cs.wordProd word_t = t → ∀ v : B → ℝ,
    wordSigma M word_t v = generalizedReflection M α v :=
-- proof
  wordSigma_reflection_root_neg

end CoxeterGroup

namespace CoxeterGroup

/--
[conj_simpleReflection_eq_generalizedReflection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ReflectionLengthDecrease.lean)
-/
@[path]
private lemma conj_simpleReflection_eq_generalizedReflection
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {w : W}
  {s : B} :
-- imply
  ∀ v : B → ℝ,
    (coxeterRepresentation M cs (w * cs.simple s * w⁻¹)) v =
      generalizedReflection M (coxeterRepresentation M cs w (e s)) v := by
-- proof
  obtain ⟨word_w, _, hprod_w⟩ := cs.exists_isReduced w
  obtain ⟨word_t, _, hprod_t⟩ := cs.exists_isReduced (w * cs.simple s * w⁻¹)
  have hprod_eq : cs.wordProd word_t =
    cs.wordProd word_w * cs.simple s * (cs.wordProd word_w)⁻¹ := by
    rw [← hprod_w]
    exact hprod_t.symm
  intro v
  have hlhs : (coxeterRepresentation M cs (w * cs.simple s * w⁻¹)) v =
    wordSigma M word_t v := by
    rw [hprod_t, coxeterRepresentation_wordProd_apply]
  have hroot : (coxeterRepresentation M cs w) (e s) = wordSigma M word_w (e s) := by
    rw [hprod_w, coxeterRepresentation_wordProd_apply]
  rw [hlhs, hroot]
  exact wordSigma_reflection_root_neg (word_u := word_w) (j := s) word_t hprod_eq v

end CoxeterGroup


-- created on 2026-10-23
-- updated on 2026-10-24
