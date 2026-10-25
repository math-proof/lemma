import Mathlib
import sympy.Basic
import Def.v1.Atlas.TheoryOfComputation.code.Clique.Part6
open ThreeSATToClique CliqueReduction
open SimpleGraph
open TuringMachine NPCompleteness ThreeSATToClique ThreeSATComplete


namespace ThreeSATToClique

/--
[Literal.IsContradictory.symm'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean)
-/
@[path]
lemma Literal.IsContradictory.symm'
  {l₁ l₂ : Literal}
-- given
  (h : l₁.IsContradictory l₂) :
-- imply
  l₂.IsContradictory l₁ :=
-- proof
  ⟨h.1.symm, fun h' => h.2 h'.symm⟩

end ThreeSATToClique

namespace ThreeSATToClique

/--
[contradictory_not_both_true](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean)
-/
@[path]
lemma contradictory_not_both_true
  {l₁ l₂ : Literal}
  {σ : ℕ → Bool}
-- given
  (hc : l₁.IsContradictory l₂)
  (h₁ : l₁.eval σ = true)
  (h₂ : l₂.eval σ = true) :
-- imply
  False := by
-- proof
  obtain ⟨hvar, hpol⟩ := hc
  cases hl₁ : l₁.pol <;> cases hl₂ : l₂.pol <;> simp_all [Literal.eval]

end ThreeSATToClique

namespace ThreeSATToClique

/--
[ThreeClause.trueLitPos_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean)
-/
@[path]
lemma ThreeClause.trueLitPos_spec
  {σ : ℕ → Bool}
  {c : ThreeClause}
-- given
  (hsat : c.isSatBy σ) :
-- imply
  (c.literalAt (c.trueLitPos σ hsat)).eval σ = true :=
-- proof
  hsat.choose_spec

end ThreeSATToClique

namespace ThreeSATToClique

/--
[satisfyingClique_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean)
-/
@[path]
lemma satisfyingClique_card
  {φ : ThreeCNF}
  {σ : ℕ → Bool}
-- given
  (hsat : ∀ (i : Fin φ.length), (φ.get i).isSatBy σ) :
-- imply
  (satisfyingClique φ σ hsat).card = φ.length := by
-- proof
  simp only [satisfyingClique]
  rw [Finset.card_image_of_injective]
  · simp [Finset.card_univ, Fintype.card_fin]
  · intro i₁ i₂ h
    exact (Prod.ext_iff.mp h).1

end ThreeSATToClique

namespace ThreeSATToClique

/--
[satisfyingClique_isClique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean)
-/
@[path]
lemma satisfyingClique_isClique
  {φ : ThreeCNF}
  {σ : ℕ → Bool}
-- given
  (hsat : ∀ (i : Fin φ.length), (φ.get i).isSatBy σ) :
-- imply
  (reductionGraph φ).IsClique (satisfyingClique φ σ hsat : Set _) := by
-- proof
  rw [SimpleGraph.isClique_iff]
  intro v₁ hv₁ v₂ hv₂ hne
  simp only [satisfyingClique, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_range] at hv₁ hv₂
  obtain ⟨i₁, rfl⟩ := hv₁
  obtain ⟨i₂, rfl⟩ := hv₂
  refine ⟨hne, ?_, ?_⟩
  · intro heq
    exact hne (by rw [show i₁ = i₂ from heq])
  · intro hc
    exact contradictory_not_both_true hc
      (ThreeClause.trueLitPos_spec σ (φ.get i₁) (hsat i₁))
      (ThreeClause.trueLitPos_spec σ (φ.get i₂) (hsat i₂))

end ThreeSATToClique

namespace ThreeSATToClique

/--
[satisfiable_imp_clique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean)
-/
@[path]
lemma satisfiable_imp_clique
  {φ : ThreeCNF}
-- given
  (hsat : φ.IsSatisfiable) :
-- imply
  ∃ s : Finset (Fin φ.length × Fin 3), (reductionGraph φ).IsNClique φ.length s := by
-- proof
  obtain ⟨σ, hσ⟩ := hsat
  exact ⟨satisfyingClique φ σ hσ,
    ⟨satisfyingClique_isClique φ σ hσ,
      satisfyingClique_card φ σ hσ⟩⟩

end ThreeSATToClique

namespace ThreeSATToClique

/--
[clique_imp_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean)
-/
@[path]
lemma clique_imp_satisfiable
  {φ : ThreeCNF}
  {s : Finset (Fin φ.length × Fin 3)}
-- given
  (hclique : (reductionGraph φ).IsNClique φ.length s) :
-- imply
  φ.IsSatisfiable := by
-- proof
  classical
  obtain ⟨hcl, hcard⟩ := hclique
  have hcovers : s.image Prod.fst = Finset.univ := by
    apply Finset.eq_univ_of_card
    have : (s.image Prod.fst).card = φ.length := by
      conv_rhs => rw [← hcard]
      apply Finset.card_image_of_injOn
      intro ⟨i₁, j₁⟩ hi₁ ⟨i₂, j₂⟩ hi₂ heq
      simp only at heq
      by_contra hne
      exact (hcl (Finset.mem_coe.mpr hi₁) (Finset.mem_coe.mpr hi₂) hne).2.1 heq
    rw [this, Fintype.card_fin]
  have hnode : ∀ i : Fin φ.length, ∃ j : Fin 3, (i, j) ∈ s := by
    intro i
    have : i ∈ s.image Prod.fst := hcovers ▸ Finset.mem_univ _
    obtain ⟨⟨i', j⟩, hmem, rfl⟩ := Finset.mem_image.mp this
    exact ⟨j, hmem⟩
  let σ : ℕ → Bool := fun v =>
    if ∃ node ∈ s, ((φ.get node.1).literalAt node.2).varIdx = v ∧
      ((φ.get node.1).literalAt node.2).pol = Polarity.pos
    then true else false
  refine ⟨σ, fun i => ?_⟩
  obtain ⟨j, hj⟩ := hnode i
  refine ⟨j, ?_⟩
  simp only [Literal.eval]
  cases hpol : ((φ.get i).literalAt j).pol
  ·
    simp only [σ]
    rw [if_pos]
    exact ⟨(i, j), hj, rfl, hpol⟩
  ·
    simp only [σ, Bool.not_eq_true']
    rw [if_neg]
    push Not
    intro ⟨i', j'⟩ hmem' hvar hpol'
    by_cases heq : (i, j) = (i', j')
    ·
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [hpol] at hpol'
      exact absurd hpol' (by decide)
    ·
      exfalso
      apply (hcl (Finset.mem_coe.mpr hj) (Finset.mem_coe.mpr hmem') heq).2.2
      exact ⟨hvar.symm, by rw [hpol, hpol']; decide⟩

end ThreeSATToClique

namespace ThreeSATToClique

/--
[reduction_correct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean)
-/
@[path]
lemma reduction_correct
  {φ : ThreeCNF} :
-- imply
  φ.IsSatisfiable ↔ ∃ s : Finset (Fin φ.length × Fin 3), (reductionGraph φ).IsNClique φ.length s := by
-- proof
  constructor
  · exact satisfiable_imp_clique φ
  · rintro ⟨s, hs⟩
    exact clique_imp_satisfiable φ s hs
end ThreeSATToClique
namespace CliqueReduction
open TuringMachine NPCompleteness ThreeSATToClique ThreeSATComplete


namespace CliqueReduction

/--
[threeSATToCliqueEnc_default](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean)
-/
@[path]
lemma threeSATToCliqueEnc_default
  {w : List SATCliqueSymbol}
-- given
  (hw : ¬∃ φ : ThreeCNF, w = [.sat φ]) :
-- imply
  threeSATToCliqueEnc w = [] := by
-- proof
  cases w with
  | nil => rfl
  | cons a t =>
    cases t with
    | nil =>
      cases a with
      | sat φ => exact absurd ⟨φ, rfl⟩ hw
      | clique _ => rfl
    | cons b t' =>
      simp only [threeSATToCliqueEnc]

end CliqueReduction

namespace CliqueReduction

/--
[nil_not_mem_CLIQUEEnc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean)
-/
@[path]
lemma nil_not_mem_CLIQUEEnc
-- imply
  ([] : List SATCliqueSymbol) ∉ CLIQUEEnc := by
-- proof
  intro ⟨φ, heq, _⟩
  exact absurd heq (List.cons_ne_nil _ _).symm

end CliqueReduction

namespace CliqueReduction

/--
[reduction_enc_correct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean)
-/
@[path]
lemma reduction_enc_correct
  {φ : ThreeCNF} :
-- imply
  [SATCliqueSymbol.sat φ] ∈ ThreeSATEnc ↔ threeSATToCliqueEnc [.sat φ] ∈ CLIQUEEnc := by
-- proof
  constructor
  ·
    rintro ⟨φ', hφ'eq, hsat⟩
    have hφeq : φ' = φ := (SATCliqueSymbol.sat.inj (List.cons.inj hφ'eq).1).symm
    subst hφeq
    exact ⟨_, rfl, (reduction_correct _).mp hsat⟩
  ·
    rintro ⟨φ', heq, hclique⟩
    have hφeq : φ' = φ := (SATCliqueSymbol.clique.inj (List.cons.inj heq).1).symm
    subst hφeq
    exact ⟨_, rfl, (reduction_correct _).mpr ⟨_, hclique.choose_spec⟩⟩

end CliqueReduction

namespace CliqueReduction

/--
[threeSATToCliqueEnc_correct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean)
-/
@[path]
lemma threeSATToCliqueEnc_correct
  {w : List SATCliqueSymbol} :
-- imply
  w ∈ ThreeSATEnc ↔ threeSATToCliqueEnc w ∈ CLIQUEEnc := by
-- proof
  constructor
  · rintro ⟨φ, rfl, hsat⟩
    exact (reduction_enc_correct φ).mp ⟨φ, rfl, hsat⟩
  · intro hmem
    by_cases hw : ∃ φ : ThreeCNF, w = [.sat φ]
    · obtain ⟨φ, rfl⟩ := hw
      exact (reduction_enc_correct φ).mpr hmem
    · exfalso
      rw [threeSATToCliqueEnc_default hw] at hmem
      exact nil_not_mem_CLIQUEEnc hmem
/-- The reduction function `threeSATToCliqueEnc` is computable in polynomial
time; this is the time-complexity content of the `3SAT ≤_P CLIQUE` reduction. -/

end CliqueReduction


-- created on 2026-10-23
