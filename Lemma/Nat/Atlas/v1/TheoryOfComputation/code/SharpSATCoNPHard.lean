import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.SharpSATCoNPHard
open NPCompleteness
open TuringMachine


namespace NPCompleteness

/--
[BoolFormula.eval_eq_of_agree_on_vars](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATCoNPHard.lean)
-/
@[path]
lemma BoolFormula.eval_eq_of_agree_on_vars
  {φ : BoolFormula}
-- given
  (h : ∀ i ∈ φ.vars, σ₁ i = σ₂ i) :
-- imply
  φ.eval σ₁ = φ.eval σ₂ := by
-- proof
  induction φ with
  | var n =>
    simp only [eval]
    exact h n (Finset.mem_singleton.mpr rfl)
  | trueConst => rfl
  | falseConst => rfl
  | not ψ ih =>
    simp only [eval]
    congr 1
    exact ih (fun i hi => h i (by simp [vars]; exact hi))
  | and ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [eval]
    congr 1
    · exact ih₁ (fun i hi => h i (by simp [vars]; left; exact hi))
    · exact ih₂ (fun i hi => h i (by simp [vars]; right; exact hi))
  | or ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [eval]
    congr 1
    · exact ih₁ (fun i hi => h i (by simp [vars]; left; exact hi))
    · exact ih₂ (fun i hi => h i (by simp [vars]; right; exact hi))

end NPCompleteness

namespace NPCompleteness

/--
[BoolFormula.countSat_eq_zero_of_not_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATCoNPHard.lean)
-/
@[path]
lemma BoolFormula.countSat_eq_zero_of_not_satisfiable
  {φ : BoolFormula}
-- given
  (hunsat : ¬φ.Satisfiable) :
-- imply
  φ.countSat = 0 := by
-- proof
  unfold countSat
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro σ _ heval
  exact hunsat ⟨fun i => if h : i ∈ φ.vars then σ ⟨i, h⟩ else false, heval⟩

end NPCompleteness

namespace NPCompleteness

/--
[BoolFormula.not_satisfiable_of_countSat_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATCoNPHard.lean)
-/
@[path]
lemma BoolFormula.not_satisfiable_of_countSat_eq_zero
  {φ : BoolFormula}
-- given
  (hcount : φ.countSat = 0) :
-- imply
  ¬φ.Satisfiable := by
-- proof
  intro ⟨σ, hσ⟩
  unfold countSat at hcount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hcount
  let σ' : φ.vars → Bool := fun ⟨i, _⟩ => σ i
  have hfalse := hcount (Finset.mem_univ σ')
  simp only [Bool.not_eq_true] at hfalse
  have hagree : ∀ i ∈ φ.vars,
    (fun j => if hj : j ∈ φ.vars then σ' ⟨j, hj⟩ else false) i = σ i := by
    intro i hi
    simp [hi, σ']
  rw [φ.eval_eq_of_agree_on_vars hagree] at hfalse
  rw [hσ] at hfalse
  exact Bool.noConfusion hfalse

end NPCompleteness

namespace NPCompleteness

/--
[PolyReducible.compl_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATCoNPHard.lean)
-/
@[path]
lemma PolyReducible.compl_left
  {enc : SharpSATEncoding}
  {Γ : Type}
  {A B : Set (List Γ)}
-- given
  (h : PolyReducible Aᶜ B) :
-- imply
  PolyReducible A Bᶜ := by
-- proof
  obtain ⟨f, hf_poly, hf_red⟩ := h
  exact ⟨f, hf_poly, fun w => by
    simp only [Set.mem_compl_iff]
    constructor
    · intro hw hfB
      exact ((hf_red w).mpr hfB) hw
    · intro hfnB
      by_contra hwnA
      exact hfnB ((hf_red w).mp hwnA)⟩

end NPCompleteness

namespace NPCompleteness

/--
[BoolFormula.not_satisfiable_falseConst](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATCoNPHard.lean)
-/
@[path]
lemma BoolFormula.not_satisfiable_falseConst
  {enc : SharpSATEncoding} :
-- imply
  ¬BoolFormula.falseConst.Satisfiable := by
-- proof
  intro ⟨σ, hσ⟩
  simp [eval] at hσ

end NPCompleteness

namespace NPCompleteness

/--
[BoolFormula.countSat_falseConst](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATCoNPHard.lean)
-/
@[path]
lemma BoolFormula.countSat_falseConst
  {enc : SharpSATEncoding} :
-- imply
  BoolFormula.falseConst.countSat = 0 :=
-- proof
  countSat_eq_zero_of_not_satisfiable not_satisfiable_falseConst

end NPCompleteness

namespace NPCompleteness

/--
[unsatToSharpSAT_correct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATCoNPHard.lean)
-/
@[path]
lemma unsatToSharpSAT_correct
  {enc : SharpSATEncoding} :
-- imply
  ∀ w : List BoolFormula, w ∈ SATLangᶜ ↔ unsatToSharpSAT enc w ∈ SharpSATLang enc := by
-- proof
  intro w
  simp only [Set.mem_compl_iff, SATLang, Set.mem_setOf_eq,
    SharpSATLang, Set.mem_setOf_eq, unsatToSharpSAT]
  constructor
  · intro hw
    push Not at hw
    match w with
    | [φ] =>
      have hunsat : ¬φ.Satisfiable := hw φ rfl
      exact ⟨φ, 0, enc.decode_encode (φ, 0),
        (BoolFormula.countSat_eq_zero_of_not_satisfiable hunsat).symm⟩
    | [] =>
      exact ⟨BoolFormula.falseConst, 0, enc.decode_encode _,
        BoolFormula.countSat_falseConst.symm⟩
    | a :: b :: rest =>
      exact ⟨BoolFormula.falseConst, 0, enc.decode_encode _,
        BoolFormula.countSat_falseConst.symm⟩
  · intro ⟨φ', k, hdec, hk⟩
    push Not
    intro ψ hw_eq
    subst hw_eq
    simp only at hdec
    have hdec0 := enc.decode_encode (ψ, 0)
    rw [hdec0] at hdec
    have hinj := Option.some_injective _ hdec
    have hφ'_eq : φ' = ψ := ((Prod.ext_iff.mp hinj).1).symm
    have hk_eq : k = 0 := ((Prod.ext_iff.mp hinj).2).symm
    subst hφ'_eq; subst hk_eq
    exact BoolFormula.not_satisfiable_of_countSat_eq_zero (by omega)
/--
The reduction function `unsatToSharpSAT` is computable in polynomial time:
encoding `⟨φ, 0⟩` from `φ` takes polynomial work in `|φ|`.
-/

end NPCompleteness


-- created on 2026-10-23
