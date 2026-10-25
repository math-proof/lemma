import Mathlib
import sympy.Basic
import Def.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part8
open TuringMachine in NPCompleteness CookLevin ThreeSATComplete HamiltonianPath
open TuringMachine NPCompleteness


namespace CookLevin

/--
[satNTM_runsInTime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma satNTM_runsInTime
-- imply
  satNTM.runsInTime (fun n => n + 2) := by
-- proof
  intro w k branch hk hstart hsteps hle
  have hstate0 : (branch ⟨0, Nat.zero_lt_succ k⟩).state = .start := by
    rw [hstart]; rfl
  suffices h : ∀ j : ℕ, (hj : j < k + 1) → 1 ≤ j →
    satNTM.isHaltConfig (branch ⟨j, hj⟩) from
    h k (Nat.lt_succ_of_le le_rfl) hk
  intro j hj hj1
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hjj : j = 0
    · subst hjj
      have hs0 := hsteps ⟨0, hk⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hs0
      unfold NTM.step at hs0
      simp only [satNTM, hstate0, show (SATState.start = SATState.accept ∨
        SATState.start = SATState.reject) = False from by decide, ite_false] at hs0
      obtain ⟨q', _, _, hmem, heq⟩ := hs0
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, satNTM]
      have hst : (branch ⟨1, hj⟩).state = q' := by
        have := congr_arg Config.state heq; simpa using this
      rw [hst]
      split_ifs at hmem <;> {
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rw [hmem.1]; simp
      }
    · have ihj : 1 ≤ j := by omega
      have ihjlt : j < k + 1 := by omega
      have ih_halt := ih ihjlt ihj
      have hstep := hsteps ⟨j, by omega⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hstep
      have hstate_halt : (branch ⟨j, ihjlt⟩).state = SATState.accept ∨
        (branch ⟨j, ihjlt⟩).state = SATState.reject := by
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, satNTM] at ih_halt
        exact ih_halt
      unfold NTM.step at hstep
      simp only [satNTM] at hstep
      obtain hst | hst <;> := hstate_halt
        simp only [hst, or_true, true_or, ite_true] at hstep <;> {
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, satNTM]
        have : (branch ⟨j + 1, hj⟩).state = (branch ⟨j, ihjlt⟩).state := by
          have := congr_arg Config.state hstep; simpa using this
        rw [this, hst]; simp
      }

end CookLevin

namespace CookLevin

/--
[satNTM_time_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma satNTM_time_bound
-- imply
  IsBigO (fun n => n + 2) (fun n => n ^ 1) := by
-- proof
  refine ⟨3, 2, by omega, ?_⟩
  intro n hn
  simp only [Nat.pow_one]
  omega
/-- Existential witness that there is a polynomial-time NTM deciding `SATLang`,
which is what `InNP SATLang` unfolds to. -/
end CookLevin
namespace TuringMachine
open TuringMachine
/-- Composition of polynomial-time computable functions is polynomial-time computable. -/
end TuringMachine
namespace ThreeSATComplete
open TuringMachine NPCompleteness


namespace ThreeSATComplete

/--
[threeSATNTM_runsInTime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma threeSATNTM_runsInTime
-- imply
  threeSATNTM.runsInTime (fun n => n + 2) := by
-- proof
  intro w k branch hk hstart hsteps hle
  have hstate0 : (branch ⟨0, Nat.zero_lt_succ k⟩).state = .start := by
    rw [hstart]; rfl
  suffices h : ∀ j : ℕ, (hj : j < k + 1) → 1 ≤ j →
    threeSATNTM.isHaltConfig (branch ⟨j, hj⟩) from
    h k (Nat.lt_succ_of_le le_rfl) hk
  intro j hj hj1
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hjj : j = 0
    · subst hjj
      have hs0 := hsteps ⟨0, hk⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hs0
      unfold NTM.step at hs0
      simp only [threeSATNTM, hstate0, show (ThreeSATState.start = ThreeSATState.accept ∨
        ThreeSATState.start = ThreeSATState.reject) = False from by decide, ite_false] at hs0
      obtain ⟨q', _, _, hmem, heq⟩ := hs0
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, threeSATNTM]
      have hst : (branch ⟨1, hj⟩).state = q' := by
        have := congr_arg Config.state heq; simpa using this
      rw [hst]
      split_ifs at hmem <;> {
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rw [hmem.1]; simp
      }
    · have ihj : 1 ≤ j := by omega
      have ihjlt : j < k + 1 := by omega
      have ih_halt := ih ihjlt ihj
      have hstep := hsteps ⟨j, by omega⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hstep
      have hstate_halt : (branch ⟨j, ihjlt⟩).state = ThreeSATState.accept ∨
        (branch ⟨j, ihjlt⟩).state = ThreeSATState.reject := by
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, threeSATNTM] at ih_halt
        exact ih_halt
      unfold NTM.step at hstep
      simp only [threeSATNTM] at hstep
      obtain hst | hst <;> := hstate_halt
        simp only [hst, or_true, true_or, ite_true] at hstep <;> {
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, threeSATNTM]
        have : (branch ⟨j + 1, hj⟩).state = (branch ⟨j, ihjlt⟩).state := by
          have := congr_arg Config.state hstep; simpa using this
        rw [this, hst]; simp
      }

end ThreeSATComplete

namespace ThreeSATComplete

/--
[threeSATNTM_time_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma threeSATNTM_time_bound
-- imply
  IsBigO (fun n => n + 2) (fun n => n ^ 1) := by
-- proof
  refine ⟨3, 2, by omega, ?_⟩
  intro n hn
  simp only [Nat.pow_one]
  omega

end ThreeSATComplete

namespace ThreeSATComplete

/--
[literal_clauseLength_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma literal_clauseLength_eq_one
  {l : BoolFormula}
-- given
  (hl : l.IsLiteral) :
-- imply
  l.clauseLength = 1 := by
-- proof
  cases l with
  | var _ => rfl
  | not inner =>
    cases inner with
    | var _ => rfl
    | _ => exact absurd hl (by simp [BoolFormula.IsLiteral])
  | _ => exact absurd hl (by simp [BoolFormula.IsLiteral])

end ThreeSATComplete

namespace ThreeSATComplete

/--
[mk3Clause_isClause](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma mk3Clause_isClause
  {l₁ l₂ l₃ : BoolFormula}
-- given
  (h₁ : l₁.IsLiteral)
  (h₂ : l₂.IsLiteral)
  (h₃ : l₃.IsLiteral) :
-- imply
  (mk3Clause l₁ l₂ l₃).IsClause := by
-- proof
  unfold mk3Clause
  show l₁.IsLiteral ∧ (BoolFormula.or l₂ l₃).IsClause
  refine ⟨h₁, ?_⟩
  show l₂.IsLiteral ∧ l₃.IsClause
  refine ⟨h₂, ?_⟩
  cases l₃ with
  | var _ => exact h₃
  | not inner =>
    cases inner with
    | var _ => exact h₃
    | _ => exact absurd h₃ (by simp [BoolFormula.IsLiteral])
  | _ => exact absurd h₃ (by simp [BoolFormula.IsLiteral])

end ThreeSATComplete

namespace ThreeSATComplete

/--
[mk3Clause_clauseLength](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma mk3Clause_clauseLength
  {l₁ l₂ l₃ : BoolFormula}
-- given
  (_h₁ : l₁.IsLiteral)
  (_h₂ : l₂.IsLiteral)
  (h₃ : l₃.IsLiteral) :
-- imply
  (mk3Clause l₁ l₂ l₃).clauseLength = 3 := by
-- proof
  unfold mk3Clause
  simp only [BoolFormula.clauseLength]
  rw [literal_clauseLength_eq_one h₃]

end ThreeSATComplete

namespace ThreeSATComplete

/--
[mk3Clause_is3Clause](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma mk3Clause_is3Clause
  {l₁ l₂ l₃ : BoolFormula}
-- given
  (h₁ : l₁.IsLiteral)
  (h₂ : l₂.IsLiteral)
  (h₃ : l₃.IsLiteral) :
-- imply
  (mk3Clause l₁ l₂ l₃).Is3Clause :=
-- proof
  ⟨mk3Clause_isClause h₁ h₂ h₃, mk3Clause_clauseLength h₁ h₂ h₃⟩

end ThreeSATComplete

namespace ThreeSATComplete

/--
[var_isLiteral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma var_isLiteral
  {n : ℕ} :
-- imply
  (BoolFormula.var n).IsLiteral :=
-- proof
  trivial

end ThreeSATComplete

namespace ThreeSATComplete

/--
[not_var_isLiteral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma not_var_isLiteral
  {n : ℕ} :
-- imply
  (BoolFormula.not (.var n)).IsLiteral :=
-- proof
  trivial

end ThreeSATComplete

namespace ThreeSATComplete

/--
[tseitinAux_clauses_are_3clauses](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma tseitinAux_clauses_are_3clauses
  {φ : BoolFormula}
  {fresh : ℕ} :
-- imply
  ∀ c ∈ (tseitinAux φ fresh).2.1, c.Is3Clause := by
-- proof
  induction φ generalizing fresh with
  | var _ => simp [tseitinAux]
  | trueConst =>
    simp only [tseitinAux]
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact mk3Clause_is3Clause (var_isLiteral _) (var_isLiteral _) (var_isLiteral _)
  | falseConst =>
    simp only [tseitinAux]
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact mk3Clause_is3Clause (not_var_isLiteral _) (not_var_isLiteral _) (not_var_isLiteral _)
  | not ψ ih =>
    simp only [tseitinAux]
    intro c hc
    have : c ∈ (tseitinAux ψ fresh).2.1 ++
      [mk3Clause (.var (tseitinAux ψ fresh).1) (.var (tseitinAux ψ fresh).2.2) (.var (tseitinAux ψ fresh).2.2),
        mk3Clause (.not (.var (tseitinAux ψ fresh).1)) (.not (.var (tseitinAux ψ fresh).2.2)) (.not (.var (tseitinAux ψ fresh).2.2))] := by
      generalize tseitinAux ψ fresh = r at hc ⊢
      obtain ⟨vφ, clsφ, fresh1⟩ := r
      exact hc
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at this
    obtain hc' | rfl | rfl := this
    · exact ih fresh c hc'
    · exact mk3Clause_is3Clause (var_isLiteral _) (var_isLiteral _) (var_isLiteral _)
    · exact mk3Clause_is3Clause (not_var_isLiteral _) (not_var_isLiteral _) (not_var_isLiteral _)
  | and ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [tseitinAux]
    intro c hc
    have : c ∈ (tseitinAux ψ₁ fresh).2.1 ++ (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.1 ++
      [mk3Clause (.not (.var (tseitinAux ψ₁ fresh).1)) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1)) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2),
        mk3Clause (.var (tseitinAux ψ₁ fresh).1) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1)) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2)),
        mk3Clause (.not (.var (tseitinAux ψ₁ fresh).1)) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2)),
        mk3Clause (.var (tseitinAux ψ₁ fresh).1) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2))] := by
      generalize tseitinAux ψ₁ fresh = r₁ at hc ⊢
      obtain ⟨v₁, cls₁, fresh1⟩ := r₁
      generalize tseitinAux ψ₂ fresh1 = r₂ at hc ⊢
      obtain ⟨v₂, cls₂, fresh2⟩ := r₂
      exact hc
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at this
    obtain (hc' | hc') | rfl | rfl | rfl | rfl := this
    · exact ih₁ fresh c hc'
    · exact ih₂ (tseitinAux ψ₁ fresh).2.2 c hc'
    · exact mk3Clause_is3Clause (not_var_isLiteral _) (not_var_isLiteral _) (var_isLiteral _)
    · exact mk3Clause_is3Clause (var_isLiteral _) (not_var_isLiteral _) (not_var_isLiteral _)
    · exact mk3Clause_is3Clause (not_var_isLiteral _) (var_isLiteral _) (not_var_isLiteral _)
    · exact mk3Clause_is3Clause (var_isLiteral _) (var_isLiteral _) (not_var_isLiteral _)
  | or ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [tseitinAux]
    intro c hc
    have : c ∈ (tseitinAux ψ₁ fresh).2.1 ++ (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.1 ++
      [mk3Clause (.not (.var (tseitinAux ψ₁ fresh).1)) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1)) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2),
        mk3Clause (.var (tseitinAux ψ₁ fresh).1) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1)) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2),
        mk3Clause (.not (.var (tseitinAux ψ₁ fresh).1)) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2),
        mk3Clause (.var (tseitinAux ψ₁ fresh).1) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2))] := by
      generalize tseitinAux ψ₁ fresh = r₁ at hc ⊢
      obtain ⟨v₁, cls₁, fresh1⟩ := r₁
      generalize tseitinAux ψ₂ fresh1 = r₂ at hc ⊢
      obtain ⟨v₂, cls₂, fresh2⟩ := r₂
      exact hc
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at this
    obtain (hc' | hc') | rfl | rfl | rfl | rfl := this
    · exact ih₁ fresh c hc'
    · exact ih₂ (tseitinAux ψ₁ fresh).2.2 c hc'
    · exact mk3Clause_is3Clause (not_var_isLiteral _) (not_var_isLiteral _) (var_isLiteral _)
    · exact mk3Clause_is3Clause (var_isLiteral _) (not_var_isLiteral _) (var_isLiteral _)
    · exact mk3Clause_is3Clause (not_var_isLiteral _) (var_isLiteral _) (var_isLiteral _)
    · exact mk3Clause_is3Clause (var_isLiteral _) (var_isLiteral _) (not_var_isLiteral _)

end ThreeSATComplete

namespace ThreeSATComplete

/--
[is3CNF_of_is3Clause](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma is3CNF_of_is3Clause
  {φ : BoolFormula}
-- given
  (h : φ.Is3Clause) :
-- imply
  φ.Is3CNF := by
-- proof
  cases φ with
  | and _ _ =>
    exact absurd h.1 (by simp [BoolFormula.IsClause, BoolFormula.IsLiteral])
  | _ => exact h

end ThreeSATComplete

namespace ThreeSATComplete

/--
[conjoinClauses_is3CNF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma conjoinClauses_is3CNF
  {cs : List BoolFormula}
-- given
  (hne : cs ≠ [])
  (h3 : ∀ c ∈ cs, c.Is3Clause) :
-- imply
  (conjoinClauses cs).Is3CNF := by
-- proof
  induction cs with
  | nil => exact absurd rfl hne
  | cons c cs ih =>
    match cs, ih with
    | [], _ =>
      simp only [conjoinClauses]
      exact is3CNF_of_is3Clause (h3 c List.mem_cons_self)
    | d :: ds, ih =>
      simp only [conjoinClauses]
      exact ⟨h3 c List.mem_cons_self,
        ih (List.cons_ne_nil d ds)
          (fun x hx => h3 x (List.mem_cons_of_mem _ hx))⟩

end ThreeSATComplete

namespace ThreeSATComplete

/--
[tseitinTransform_is3CNF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma tseitinTransform_is3CNF
  {φ : BoolFormula} :
-- imply
  (tseitinTransform φ).Is3CNF := by
-- proof
  unfold tseitinTransform
  set fresh := maxVarSucc φ
  have hroot : (mk3Clause (.var (tseitinAux φ fresh).1)
    (.var (tseitinAux φ fresh).1)
    (.var (tseitinAux φ fresh).1)).Is3Clause :=
    mk3Clause_is3Clause (var_isLiteral _) (var_isLiteral _) (var_isLiteral _)
  have hclauses := tseitinAux_clauses_are_3clauses φ fresh
  apply conjoinClauses_is3CNF
  · exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  · intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    obtain hc | hc := hc
    · exact hclauses c hc
    · subst hc; exact hroot

end ThreeSATComplete

namespace ThreeSATComplete

/--
[tseitinAux_fresh_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma tseitinAux_fresh_mono
-- imply
  ∀ (φ : BoolFormula) (fresh : ℕ), fresh ≤ (tseitinAux φ fresh).2.2 :=
-- proof
  tseitinAux_fresh_mono ψ fresh
    generalize hr : tseitinAux ψ fresh = r at h; obtain ⟨_, _, f1⟩ := r; simp only at h ⊢; omega
    | .and ψ₁ ψ₂, fresh => by
      simp only [tseitinAux]
      have h1 := tseitinAux_fresh_mono ψ₁ fresh
      generalize hr₁ : tseitinAux ψ₁ fresh = r₁ at h1; obtain ⟨_, _, f1⟩ := r₁; simp only at h1 ⊢
      have h2 := tseitinAux_fresh_mono ψ₂ f1
      generalize hr₂ : tseitinAux ψ₂ f1 = r₂ at h2; obtain ⟨_, _, f2⟩ := r₂; simp only at h2 ⊢; omega
    | .or ψ₁ ψ₂, fresh => by
      simp only [tseitinAux]
      have h1 := tseitinAux_fresh_mono ψ₁ fresh
      generalize hr₁ : tseitinAux ψ₁ fresh = r₁ at h1; obtain ⟨_, _, f1⟩ := r₁; simp only at h1 ⊢
      have h2 := tseitinAux_fresh_mono ψ₂ f1
      generalize hr₂ : tseitinAux ψ₂ f1 = r₂ at h2; obtain ⟨_, _, f2⟩ := r₂; simp only at h2 ⊢; omega

end ThreeSATComplete

namespace ThreeSATComplete

/--
[eval_eq_of_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma eval_eq_of_ge
  {c : BoolFormula}
  {σ₁ σ₂ : BoolAssignment}
-- given
  (h : ∀ n, n < fmv c → σ₁ n = σ₂ n) :
-- imply
  c.eval σ₁ = c.eval σ₂ := by
-- proof
  induction c with
  | var n => exact h n (by simp [fmv])
  | trueConst | falseConst => rfl
  | not ψ ih => simp only [BoolFormula.eval]; congr 1; exact ih fun n hn => h n (by simp [fmv] at hn ⊢; exact hn)
  | and ψ₁ ψ₂ ih₁ ih₂ | or ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [BoolFormula.eval]; congr 1
    · exact ih₁ fun n hn => h n (by simp [fmv] at hn ⊢; omega)
    · exact ih₂ fun n hn => h n (by simp [fmv] at hn ⊢; omega)

end ThreeSATComplete

namespace ThreeSATComplete

/--
[tseitinAux_root_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma tseitinAux_root_bound
  {φ : BoolFormula}
  {fresh : ℕ}
-- given
  (hfr : maxVarSucc φ ≤ fresh) :
-- imply
  (tseitinAux φ fresh).1 < (tseitinAux φ fresh).2.2 := by
-- proof
  cases φ with
  | var n => simp [tseitinAux, maxVarSucc] at hfr ⊢; omega
  | trueConst => simp [tseitinAux]
  | falseConst => simp [tseitinAux]
  | not ψ => simp only [tseitinAux]; generalize tseitinAux ψ fresh = r; obtain ⟨_, _, f1⟩ := r; simp only; omega
  | and ψ₁ ψ₂ => simp only [tseitinAux]; generalize tseitinAux ψ₁ fresh = r₁; obtain ⟨_, _, f1⟩ := r₁; simp only; generalize tseitinAux ψ₂ f1 = r₂; obtain ⟨_, _, f2⟩ := r₂; simp only; omega
  | or ψ₁ ψ₂ => simp only [tseitinAux]; generalize tseitinAux ψ₁ fresh = r₁; obtain ⟨_, _, f1⟩ := r₁; simp only; generalize tseitinAux ψ₂ f1 = r₂; obtain ⟨_, _, f2⟩ := r₂; simp only; omega

end ThreeSATComplete

namespace ThreeSATComplete

/--
[tseitinAux_clause_fmv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma tseitinAux_clause_fmv
  {φ : BoolFormula}
  {fresh : ℕ}
-- given
  (hfr : maxVarSucc φ ≤ fresh) :
-- imply
  ∀ c ∈ (tseitinAux φ fresh).2.1, fmv c ≤ (tseitinAux φ fresh).2.2 := by
-- proof
  induction φ generalizing fresh with
  | var _ => simp [tseitinAux]
  | trueConst => intro c hc; simp only [tseitinAux, List.mem_cons, List.mem_nil_iff, or_false] at hc ⊢; subst hc; simp [mk3Clause, fmv]
  | falseConst => intro c hc; simp only [tseitinAux, List.mem_cons, List.mem_nil_iff, or_false] at hc ⊢; subst hc; simp [mk3Clause, fmv]
  | not ψ ih =>
    have hfrs : maxVarSucc ψ ≤ fresh := by simp [maxVarSucc] at hfr; exact hfr
    simp only [tseitinAux] at *; generalize hr : tseitinAux ψ fresh = r at *; obtain ⟨vφ, clsφ, f1⟩ := r; simp only at *
    have hvlt : vφ < f1 := by have := tseitinAux_root_bound ψ fresh hfrs; rw [hr] at this; simp only at this; exact this
    intro c hc; simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    obtain hc | rfl | rfl := hc
    · have := ih fresh hfrs c (by rw [hr]; exact hc); rw [hr] at this; simp only at this; omega
    · simp [mk3Clause, fmv]; omega
    · simp [mk3Clause, fmv]; omega
  | and ψ₁ ψ₂ ih₁ ih₂ =>
    have hfr₁ : maxVarSucc ψ₁ ≤ fresh := by simp [maxVarSucc] at hfr; omega
    simp only [tseitinAux] at *
    generalize hr₁ : tseitinAux ψ₁ fresh = r₁ at *; obtain ⟨v₁, cls₁, f1⟩ := r₁; simp only at *
    have hfr₂ : maxVarSucc ψ₂ ≤ f1 := by simp [maxVarSucc] at hfr; have := tseitinAux_fresh_mono ψ₁ fresh; rw [hr₁] at this; simp only at this; omega
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂ at *; obtain ⟨v₂, cls₂, f2⟩ := r₂; simp only at *
    have hv₁lt : v₁ < f2 := by have := tseitinAux_root_bound ψ₁ fresh hfr₁; rw [hr₁] at this; have := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at this; simp only at *; omega
    have hv₂lt : v₂ < f2 := by have := tseitinAux_root_bound ψ₂ f1 hfr₂; rw [hr₂] at this; simp only at this; exact this
    intro c hc; simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    obtain (hc | hc) | rfl | rfl | rfl | rfl := hc
    · have := ih₁ fresh hfr₁ c (by rw [hr₁]; exact hc); rw [hr₁] at this; have hm := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at hm; simp only at *; omega
    · have := ih₂ f1 hfr₂ c (by rw [hr₂]; exact hc); rw [hr₂] at this; simp only at this; omega
    all_goals simp [mk3Clause, fmv]; omega
  | or ψ₁ ψ₂ ih₁ ih₂ =>
    have hfr₁ : maxVarSucc ψ₁ ≤ fresh := by simp [maxVarSucc] at hfr; omega
    simp only [tseitinAux] at *
    generalize hr₁ : tseitinAux ψ₁ fresh = r₁ at *; obtain ⟨v₁, cls₁, f1⟩ := r₁; simp only at *
    have hfr₂ : maxVarSucc ψ₂ ≤ f1 := by simp [maxVarSucc] at hfr; have := tseitinAux_fresh_mono ψ₁ fresh; rw [hr₁] at this; simp only at this; omega
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂ at *; obtain ⟨v₂, cls₂, f2⟩ := r₂; simp only at *
    have hv₁lt : v₁ < f2 := by have := tseitinAux_root_bound ψ₁ fresh hfr₁; rw [hr₁] at this; have := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at this; simp only at *; omega
    have hv₂lt : v₂ < f2 := by have := tseitinAux_root_bound ψ₂ f1 hfr₂; rw [hr₂] at this; simp only at this; exact this
    intro c hc; simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    obtain (hc | hc) | rfl | rfl | rfl | rfl := hc
    · have := ih₁ fresh hfr₁ c (by rw [hr₁]; exact hc); rw [hr₁] at this; have hm := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at hm; simp only at *; omega
    · have := ih₂ f1 hfr₂ c (by rw [hr₂]; exact hc); rw [hr₂] at this; simp only at this; omega
    all_goals simp [mk3Clause, fmv]; omega

end ThreeSATComplete

namespace ThreeSATComplete

/--
[eval_maxVarSucc_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma eval_maxVarSucc_le
  {φ : BoolFormula}
  {fresh : ℕ}
  {σ σ' : BoolAssignment}
-- given
  (hfr : maxVarSucc φ ≤ fresh)
  (h : ∀ n, n < fresh → σ' n = σ n) :
-- imply
  φ.eval σ' = φ.eval σ := by
-- proof
  apply eval_eq_of_ge; intro n hn; apply h
  induction φ with
  | var m => simp [fmv] at hn; simp [maxVarSucc] at hfr; omega
  | trueConst | falseConst => simp [fmv] at hn
  | not ψ ih => simp [fmv, maxVarSucc] at hn hfr; exact ih hfr hn
  | and ψ₁ ψ₂ ih₁ ih₂ | or ψ₁ ψ₂ ih₁ ih₂ =>
    simp [fmv, maxVarSucc] at hn hfr; rcases hn with hn | hn
    · exact ih₁ (by omega) hn
    · exact ih₂ (by omega) hn

end ThreeSATComplete

namespace ThreeSATComplete

/--
[tseitinAux_completeness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma tseitinAux_completeness
  {φ : BoolFormula}
  {fresh : ℕ}
  {σ : BoolAssignment}
-- given
  (hfr : maxVarSucc φ ≤ fresh) :
-- imply
  ∃ σ' : BoolAssignment, (∀ n, n < fresh → σ' n = σ n) ∧ σ' (tseitinAux φ fresh).1 = φ.eval σ ∧ (∀ c ∈ (tseitinAux φ fresh).2.1, c.eval σ' = true) := by
-- proof
  induction φ generalizing fresh σ with
  | var n =>
    simp only [tseitinAux, BoolFormula.eval]
    exact ⟨σ, fun _ _ => rfl, rfl, fun _ h => absurd h (by simp)⟩
  | trueConst =>
    simp only [tseitinAux, BoolFormula.eval]
    exact ⟨Function.update σ fresh true, fun n hn => by simp [Function.update_apply, Nat.ne_of_lt hn], by simp [Function.update_apply],
      fun c hc => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc; subst hc; simp [mk3Clause, BoolFormula.eval, Function.update_apply]⟩
  | falseConst =>
    simp only [tseitinAux, BoolFormula.eval]
    exact ⟨Function.update σ fresh false, fun n hn => by simp [Function.update_apply, Nat.ne_of_lt hn], by simp [Function.update_apply],
      fun c hc => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc; subst hc; simp [mk3Clause, BoolFormula.eval, Function.update_apply]⟩
  | not ψ ih =>
    simp only [tseitinAux]; generalize hr : tseitinAux ψ fresh = r; obtain ⟨vφ, clsφ, f1⟩ := r; simp only
    have hfrs : maxVarSucc ψ ≤ fresh := by simp [maxVarSucc] at hfr; exact hfr
    obtain ⟨σ₁, hσ₁a, hσ₁r, hσ₁c⟩ := ih fresh σ hfrs; rw [hr] at hσ₁r hσ₁c; simp only at *
    have hvlt : vφ < f1 := by have := tseitinAux_root_bound ψ fresh hfrs; rw [hr] at this; exact this
    have hfge : fresh ≤ f1 := by have := tseitinAux_fresh_mono ψ fresh; rw [hr] at this; exact this
    refine ⟨Function.update σ₁ f1 (!σ₁ vφ), fun n hn => ?_, ?_, fun c hc => ?_⟩
    · simp [Function.update_apply, show n ≠ f1 from by omega]; exact hσ₁a n hn
    · simp [Function.update_apply, show vφ ≠ f1 from by omega, BoolFormula.eval, hσ₁r]
    · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
      obtain hc | rfl | rfl := hc
      · have hfmv := tseitinAux_clause_fmv ψ fresh hfrs c (by rw [hr]; exact hc); rw [hr] at hfmv; simp only at hfmv
        rw [eval_eq_of_ge c _ σ₁ (fun n hn => by simp [Function.update_apply, show n ≠ f1 from by omega])]; exact hσ₁c c hc
      · simp only [mk3Clause, BoolFormula.eval, Function.update_apply, show vφ ≠ f1 from by omega, ite_false]; cases σ₁ vφ <;> simp
      · simp only [mk3Clause, BoolFormula.eval, Function.update_apply, show vφ ≠ f1 from by omega, ite_false]; cases σ₁ vφ <;> simp
  | and ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [tseitinAux]; generalize hr₁ : tseitinAux ψ₁ fresh = r₁; obtain ⟨v₁, cls₁, f1⟩ := r₁; simp only
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂; obtain ⟨v₂, cls₂, f2⟩ := r₂; simp only
    have hfr₁ : maxVarSucc ψ₁ ≤ fresh := by simp [maxVarSucc] at hfr; omega
    have hfr₂ : maxVarSucc ψ₂ ≤ f1 := by simp [maxVarSucc] at hfr; have := tseitinAux_fresh_mono ψ₁ fresh; rw [hr₁] at this; simp only at this; omega
    obtain ⟨σ₁, hσ₁a, hσ₁r, hσ₁c⟩ := ih₁ fresh σ hfr₁; rw [hr₁] at hσ₁r hσ₁c; simp only at *
    obtain ⟨σ₂, hσ₂a, hσ₂r, hσ₂c⟩ := ih₂ f1 σ₁ hfr₂; rw [hr₂] at hσ₂r hσ₂c; simp only at *
    have hv₁lt : v₁ < f2 := by have := tseitinAux_root_bound ψ₁ fresh hfr₁; rw [hr₁] at this; have := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at this; simp only at *; omega
    have hv₂lt : v₂ < f2 := by have := tseitinAux_root_bound ψ₂ f1 hfr₂; rw [hr₂] at this; exact this
    have hfge : fresh ≤ f1 := by have := tseitinAux_fresh_mono ψ₁ fresh; rw [hr₁] at this; exact this
    have hf2ge : f1 ≤ f2 := by have := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at this; exact this
    have hσ₂_orig : ∀ n, n < fresh → σ₂ n = σ n := fun n hn => by rw [hσ₂a n (by omega)]; exact hσ₁a n hn
    have hσ₂v₁ : σ₂ v₁ = ψ₁.eval σ := by rw [hσ₂a v₁ (by have := tseitinAux_root_bound ψ₁ fresh hfr₁; rw [hr₁] at this; exact this)]; exact hσ₁r
    have hσ₂r_eq : σ₂ v₂ = ψ₂.eval σ := by rw [hσ₂r]; exact eval_maxVarSucc_le ψ₂ fresh σ σ₁ (by simp [maxVarSucc] at hfr; omega) hσ₁a
    refine ⟨Function.update σ₂ f2 (σ₂ v₁ && σ₂ v₂), fun n hn => ?_, ?_, fun c hc => ?_⟩
    · simp [Function.update_apply, show n ≠ f2 from by omega]; exact hσ₂_orig n hn
    · simp [Function.update_apply, BoolFormula.eval, hσ₂v₁, hσ₂r_eq]
    · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
      obtain (hc | hc) | rfl | rfl | rfl | rfl := hc
      · have hfmv := tseitinAux_clause_fmv ψ₁ fresh hfr₁ c (by rw [hr₁]; exact hc); rw [hr₁] at hfmv; simp only at hfmv
        rw [eval_eq_of_ge c _ σ₂ (fun n hn => by simp [Function.update_apply, show n ≠ f2 from by omega])]
        rw [eval_eq_of_ge c σ₂ σ₁ (fun n hn => by exact hσ₂a n (by omega))]; exact hσ₁c c hc
      · have hfmv := tseitinAux_clause_fmv ψ₂ f1 hfr₂ c (by rw [hr₂]; exact hc); rw [hr₂] at hfmv; simp only at hfmv
        rw [eval_eq_of_ge c _ σ₂ (fun n hn => by simp [Function.update_apply, show n ≠ f2 from by omega])]; exact hσ₂c c hc
      all_goals simp [mk3Clause, BoolFormula.eval, Function.update_apply, show v₁ ≠ f2 from by omega, show v₂ ≠ f2 from by omega]; cases σ₂ v₁ <;> cases σ₂ v₂ <;> simp
  | or ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [tseitinAux]; generalize hr₁ : tseitinAux ψ₁ fresh = r₁; obtain ⟨v₁, cls₁, f1⟩ := r₁; simp only
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂; obtain ⟨v₂, cls₂, f2⟩ := r₂; simp only
    have hfr₁ : maxVarSucc ψ₁ ≤ fresh := by simp [maxVarSucc] at hfr; omega
    have hfr₂ : maxVarSucc ψ₂ ≤ f1 := by simp [maxVarSucc] at hfr; have := tseitinAux_fresh_mono ψ₁ fresh; rw [hr₁] at this; simp only at this; omega
    obtain ⟨σ₁, hσ₁a, hσ₁r, hσ₁c⟩ := ih₁ fresh σ hfr₁; rw [hr₁] at hσ₁r hσ₁c; simp only at *
    obtain ⟨σ₂, hσ₂a, hσ₂r, hσ₂c⟩ := ih₂ f1 σ₁ hfr₂; rw [hr₂] at hσ₂r hσ₂c; simp only at *
    have hv₁lt : v₁ < f2 := by have := tseitinAux_root_bound ψ₁ fresh hfr₁; rw [hr₁] at this; have := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at this; simp only at *; omega
    have hv₂lt : v₂ < f2 := by have := tseitinAux_root_bound ψ₂ f1 hfr₂; rw [hr₂] at this; exact this
    have hfge : fresh ≤ f1 := by have := tseitinAux_fresh_mono ψ₁ fresh; rw [hr₁] at this; exact this
    have hf2ge : f1 ≤ f2 := by have := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at this; exact this
    have hσ₂_orig : ∀ n, n < fresh → σ₂ n = σ n := fun n hn => by rw [hσ₂a n (by omega)]; exact hσ₁a n hn
    have hσ₂v₁ : σ₂ v₁ = ψ₁.eval σ := by rw [hσ₂a v₁ (by have := tseitinAux_root_bound ψ₁ fresh hfr₁; rw [hr₁] at this; exact this)]; exact hσ₁r
    have hσ₂r_eq : σ₂ v₂ = ψ₂.eval σ := by rw [hσ₂r]; exact eval_maxVarSucc_le ψ₂ fresh σ σ₁ (by simp [maxVarSucc] at hfr; omega) hσ₁a
    refine ⟨Function.update σ₂ f2 (σ₂ v₁ || σ₂ v₂), fun n hn => ?_, ?_, fun c hc => ?_⟩
    · simp [Function.update_apply, show n ≠ f2 from by omega]; exact hσ₂_orig n hn
    · simp [Function.update_apply, BoolFormula.eval, hσ₂v₁, hσ₂r_eq]
    · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
      obtain (hc | hc) | rfl | rfl | rfl | rfl := hc
      · have hfmv := tseitinAux_clause_fmv ψ₁ fresh hfr₁ c (by rw [hr₁]; exact hc); rw [hr₁] at hfmv; simp only at hfmv
        rw [eval_eq_of_ge c _ σ₂ (fun n hn => by simp [Function.update_apply, show n ≠ f2 from by omega])]
        rw [eval_eq_of_ge c σ₂ σ₁ (fun n hn => by exact hσ₂a n (by omega))]; exact hσ₁c c hc
      · have hfmv := tseitinAux_clause_fmv ψ₂ f1 hfr₂ c (by rw [hr₂]; exact hc); rw [hr₂] at hfmv; simp only at hfmv
        rw [eval_eq_of_ge c _ σ₂ (fun n hn => by simp [Function.update_apply, show n ≠ f2 from by omega])]; exact hσ₂c c hc
      all_goals simp [mk3Clause, BoolFormula.eval, Function.update_apply, show v₁ ≠ f2 from by omega, show v₂ ≠ f2 from by omega]; cases σ₂ v₁ <;> cases σ₂ v₂ <;> simp

end ThreeSATComplete

namespace ThreeSATComplete

/--
[tseitinTransform_correct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma tseitinTransform_correct
  {φ : BoolFormula} :
-- imply
  φ.Satisfiable ↔ (tseitinTransform φ).Satisfiable := by
-- proof
  constructor
  · intro ⟨σ, hσ⟩
    unfold tseitinTransform BoolFormula.Satisfiable
    obtain ⟨σ', _, hσ'_root, hσ'_cls⟩ := tseitinAux_completeness φ (maxVarSucc φ) σ le_rfl
    have hne : (tseitinAux φ (maxVarSucc φ)).2.1 ++
      [mk3Clause (.var (tseitinAux φ (maxVarSucc φ)).1)
        (.var (tseitinAux φ (maxVarSucc φ)).1)
        (.var (tseitinAux φ (maxVarSucc φ)).1)] ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    refine ⟨σ', ?_⟩
    rw [conjoinClauses_eval _ hne]
    intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    obtain hc | hc := hc
    · exact hσ'_cls c hc
    · subst hc; simp [mk3Clause, BoolFormula.eval, hσ'_root, hσ]
  · intro ⟨σ, hσ⟩
    unfold tseitinTransform at hσ
    have hne : (tseitinAux φ (maxVarSucc φ)).2.1 ++
      [mk3Clause (.var (tseitinAux φ (maxVarSucc φ)).1)
        (.var (tseitinAux φ (maxVarSucc φ)).1)
        (.var (tseitinAux φ (maxVarSucc φ)).1)] ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    rw [conjoinClauses_eval _ hne] at hσ
    have hcls := fun c hc => hσ c (List.mem_append_left _ hc)
    have hroot := hσ (mk3Clause (.var (tseitinAux φ (maxVarSucc φ)).1)
      (.var (tseitinAux φ (maxVarSucc φ)).1)
      (.var (tseitinAux φ (maxVarSucc φ)).1)) (List.mem_append_right _ (by simp))
    simp [mk3Clause, BoolFormula.eval] at hroot
    exact ⟨σ, by rw [← tseitinAux_soundness φ (maxVarSucc φ) σ hcls]; exact hroot⟩

end ThreeSATComplete

namespace ThreeSATComplete

/--
[satTo3SATFn_correct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma satTo3SATFn_correct
-- imply
  ∀ w : List BoolFormula, w ∈ SATLang ↔ satTo3SATFn w ∈ ThreeSATLang := by
-- proof
  intro w
  simp only [SATLang, ThreeSATLang, Set.mem_setOf_eq]
  constructor
  · rintro ⟨φ, rfl, hsat⟩
    exact ⟨tseitinTransform φ, rfl, tseitinTransform_is3CNF φ,
      (tseitinTransform_correct φ).mp hsat⟩
  · intro ⟨ψ, hw_eq, h3cnf, hsat⟩
    match w, hw_eq with
    | [φ], hw_eq =>
      simp only [satTo3SATFn] at hw_eq
      have hψ : ψ = tseitinTransform φ := (List.cons_eq_cons.mp hw_eq).1.symm
      exact ⟨φ, rfl, (tseitinTransform_correct φ).mpr (hψ ▸ hsat)⟩
    | [], hw_eq => simp [satTo3SATFn] at hw_eq
    | _ :: _ :: _, hw_eq => simp [satTo3SATFn] at hw_eq
/-- `SAT ≤_P 3SAT` via the Tseitin transformation. -/
end ThreeSATComplete
namespace HamiltonianPath
open TuringMachine NPCompleteness

end ThreeSATComplete

namespace HamiltonianPath

/--
[hampathNTM_decides](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma hampathNTM_decides
-- imply
  hampathNTM.decides HampathLang := by
-- proof
  constructor
  ·
    intro w n branch hn hstart hsteps
    have hstate0 : (branch ⟨0, Nat.zero_lt_succ n⟩).state = .start := by
      rw [hstart]; rfl
    exact ⟨⟨1, by omega⟩, by
      have hs0 := hsteps ⟨0, hn⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hs0
      unfold NTM.step at hs0
      simp only [hampathNTM, hstate0, show (HampathState.start = HampathState.accept ∨
        HampathState.start = HampathState.reject) = False from by decide, ite_false] at hs0
      obtain ⟨q', _, _, hmem, heq⟩ := hs0
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, hampathNTM]
      have hst : (branch ⟨1, by omega⟩).state = q' := by
        have := congr_arg Config.state heq; simpa using this
      rw [hst]
      split_ifs at hmem <;> {
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rw [hmem.1]; simp
      }⟩
  ·
    ext w
    simp only [NTM.language, NTM.accepts, Set.mem_setOf_eq, HampathLang]
    constructor
    ·
      rintro ⟨n, branch, hstart, hsteps, haccept⟩
      have hstate0 : (branch ⟨0, Nat.zero_lt_succ n⟩).state = .start := by
        rw [hstart]; rfl
      have hn_pos : 0 < n := by
        by_contra h; push_neg at h
        have hn0 : n = 0 := Nat.eq_zero_of_le_zero h
        subst hn0
        simp only [NTM.isAcceptConfig, hampathNTM] at haccept
        rw [hstate0] at haccept; exact absurd haccept (by decide)
      have hs0 := hsteps ⟨0, hn_pos⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hs0
      unfold NTM.step at hs0
      simp only [hampathNTM, hstate0, show (HampathState.start = HampathState.accept ∨
        HampathState.start = HampathState.reject) = False from by decide, ite_false] at hs0
      obtain ⟨q', b', d', hmem, heq⟩ := hs0
      have hstate1 : (branch ⟨1, by omega⟩).state = q' := by
        have := congr_arg Config.state heq; simpa using this
      have hq'_cases : q' = HampathState.accept ∨ q' = HampathState.reject := by
        split_ifs at hmem <;>
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
          [exact Or.inl hmem.1; exact Or.inr hmem.1]
      have hall_eq : ∀ j : ℕ, (hj : j < n + 1) → 1 ≤ j →
        (branch ⟨j, hj⟩).state = q' := by
        intro j hj hj1
        induction j with
        | zero => omega
        | succ j ih =>
          by_cases hjj : j = 0
          · subst hjj; exact hstate1
          · have ihj : j < n + 1 := by omega
            have ih_eq := ih ihj (by omega)
            have hstep := hsteps ⟨j, by omega⟩
            simp only [Fin.castSucc_mk, Fin.succ_mk] at hstep
            unfold NTM.step at hstep
            simp only [hampathNTM] at hstep
            obtain hq | hq <;> { := hq'_cases
              rw [ih_eq, hq] at hstep
              simp only [or_true, true_or, ite_true] at hstep
              have := congr_arg Config.state hstep
              simpa [ih_eq, hq] using this
            }
      have hfinal : (branch ⟨n, Nat.lt_succ_of_le le_rfl⟩).state = q' :=
        hall_eq n (Nat.lt_succ_of_le le_rfl) hn_pos
      simp only [NTM.isAcceptConfig, hampathNTM] at haccept
      rw [hfinal] at haccept
      have hcond : (branch ⟨0, Nat.zero_lt_succ n⟩).tape
        (branch ⟨0, Nat.zero_lt_succ n⟩).headPos ≠
        HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩ ∧
        ((branch ⟨0, Nat.zero_lt_succ n⟩).tape
        (branch ⟨0, Nat.zero_lt_succ n⟩).headPos).isYesInstance := by
        split_ifs at hmem with hc
        · exact hc
        · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rw [hmem.1] at haccept; exact absurd haccept (by decide)
      have hne : w ≠ [] := by
        intro hempty
        have : (branch ⟨0, Nat.zero_lt_succ n⟩).tape
          (branch ⟨0, Nat.zero_lt_succ n⟩).headPos =
          HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
          rw [hstart]
          simp only [NTM.initConfig, hampathNTM, hempty, List.length_nil]
          split <;> [exfalso; rfl] <;> omega
        exact hcond.1 this
      have htape_eq : (branch ⟨0, Nat.zero_lt_succ n⟩).tape
        (branch ⟨0, Nat.zero_lt_succ n⟩).headPos = w.head hne := by
        rw [hstart]
        simp only [NTM.initConfig, hampathNTM]
        have hpos : (0 : ℤ) ≥ 0 ∧ (0 : ℤ) < ↑w.length := ⟨le_refl _, by
          have := List.length_pos_of_ne_nil hne; omega⟩
        simp only [hpos, dite_true, Int.toNat_zero]
        cases w with
        | nil => exact absurd rfl hne
        | cons a t => rfl
      exact ⟨w.head hne, List.head?_eq_head hne, htape_eq ▸ hcond.2⟩
    ·
      rintro ⟨sym, hhead, hyes⟩
      have hne : w ≠ [] := by intro h; simp [h] at hhead
      have hsym : w.head hne = sym := by
        have := List.head?_eq_head hne; rw [hhead] at this
        exact Option.some_injective _ this |>.symm
      set c0 := hampathNTM.initConfig w
      have hc0_state : c0.state = .start := rfl
      have hc0_tape : c0.tape c0.headPos = sym := by
        simp only [c0, NTM.initConfig, hampathNTM]
        have hpos : (0 : ℤ) ≥ 0 ∧ (0 : ℤ) < ↑w.length := ⟨le_refl _, by
          have := List.length_pos_of_ne_nil hne; omega⟩
        simp only [hpos, dite_true, Int.toNat_zero]
        cases w with
        | nil => exact absurd rfl hne
        | cons a t => simp only [List.get, List.head] at hsym ⊢; exact hsym
      have hne_blank : sym ≠ HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
        intro heq; rw [heq] at hyes
        simp only [HampathSymbol.isYesInstance, HampathSymbol.toDigraph,
          HampathSymbol.numVertices, HampathSymbol.source, HampathSymbol.target,
          DiGraph.HasHamiltonianPath, DiGraph.IsHamiltonianPath] at hyes
        obtain ⟨p, _, _, hedge, _, hall⟩ := hyes
        have h0 := hall ⟨0, by omega⟩
        have h1 := hall ⟨1, by omega⟩
        have hlen : p.length ≥ 2 := by
          obtain _ | ⟨a, _ | ⟨b, _⟩⟩ <;> simp_all := p
        have hfalse := hedge 0 (by omega)
        simp only [DiGraph.mk] at hfalse
        exact Bool.false_ne_true hfalse
      have hcond : c0.tape c0.headPos ≠
        HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩ ∧
        (c0.tape c0.headPos).isYesInstance := by
        rw [hc0_tape]; exact ⟨hne_blank, hyes⟩
      set c1 : Config HampathState HampathSymbol :=
        ⟨.accept, c0.headPos + 1, Function.update c0.tape c0.headPos (c0.tape c0.headPos)⟩
      have hstep : hampathNTM.step c0 c1 := by
        unfold NTM.step
        simp only [hampathNTM, hc0_state, show (HampathState.start = HampathState.accept ∨
          HampathState.start = HampathState.reject) = False from by decide, ite_false]
        exact ⟨.accept, c0.tape c0.headPos, Direction.R, by
          show _ ∈ hampathNTM.δ .start _
          simp only [hampathNTM]
          rw [if_pos hcond]; exact Set.mem_singleton _, rfl⟩
      have haccept_c1 : hampathNTM.isAcceptConfig c1 := by
        simp only [NTM.isAcceptConfig, hampathNTM, c1]
      refine ⟨1, fun i => match i with
        | ⟨0, _⟩ => c0
        | ⟨1, _⟩ => c1
        | ⟨n + 2, h⟩ => absurd h (by omega), rfl, ?_, ?_⟩
      · intro ⟨i, hi⟩
        have hi0 : i = 0 := by omega
        subst hi0
        simp only [Fin.castSucc_mk, Fin.succ_mk]
        exact hstep
      · exact haccept_c1

end HamiltonianPath

namespace HamiltonianPath

/--
[hampathNTM_runsInTime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma hampathNTM_runsInTime
-- imply
  hampathNTM.runsInTime (fun n => n + 2) := by
-- proof
  intro w k branch hk hstart hsteps hle
  have hstate0 : (branch ⟨0, Nat.zero_lt_succ k⟩).state = .start := by
    rw [hstart]; rfl
  suffices h : ∀ j : ℕ, (hj : j < k + 1) → 1 ≤ j →
    hampathNTM.isHaltConfig (branch ⟨j, hj⟩) from
    h k (Nat.lt_succ_of_le le_rfl) hk
  intro j hj hj1
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hjj : j = 0
    · subst hjj
      have hs0 := hsteps ⟨0, hk⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hs0
      unfold NTM.step at hs0
      simp only [hampathNTM, hstate0, show (HampathState.start = HampathState.accept ∨
        HampathState.start = HampathState.reject) = False from by decide, ite_false] at hs0
      obtain ⟨q', _, _, hmem, heq⟩ := hs0
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, hampathNTM]
      have hst : (branch ⟨1, hj⟩).state = q' := by
        have := congr_arg Config.state heq; simpa using this
      rw [hst]
      split_ifs at hmem <;> {
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rw [hmem.1]; simp
      }
    · have ihj : 1 ≤ j := by omega
      have ihjlt : j < k + 1 := by omega
      have ih_halt := ih ihjlt ihj
      have hstep := hsteps ⟨j, by omega⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hstep
      have hstate_halt : (branch ⟨j, ihjlt⟩).state = HampathState.accept ∨
        (branch ⟨j, ihjlt⟩).state = HampathState.reject := by
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, hampathNTM] at ih_halt
        exact ih_halt
      unfold NTM.step at hstep
      simp only [hampathNTM] at hstep
      obtain hst | hst <;> := hstate_halt
        simp only [hst, or_true, true_or, ite_true] at hstep <;> {
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, hampathNTM]
        have : (branch ⟨j + 1, hj⟩).state = (branch ⟨j, ihjlt⟩).state := by
          have := congr_arg Config.state hstep; simpa using this
        rw [this, hst]; simp
      }

end HamiltonianPath

namespace HamiltonianPath

/--
[hampathNTM_time_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma hampathNTM_time_bound
-- imply
  IsBigO (fun n => n + 2) (fun n => n ^ 2) := by
-- proof
  refine ⟨3, 2, by omega, ?_⟩
  intro n hn
  show n + 2 ≤ 3 * n ^ 2
  have h1 : 2 ≤ n := hn
  have h2 : n ≤ n * n := Nat.le_mul_of_pos_left n (by omega)
  have h3 : n ^ 2 = n * n := Nat.pow_two n
  omega

end HamiltonianPath

namespace HamiltonianPath

/--
[hampath_in_NP_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma hampath_in_NP_aux
-- imply
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : NTM Q HampathSymbol) (t' : ℕ → ℕ), M.decides HampathLang ∧ M.runsInTime t' ∧ IsBigO t' (fun n => n ^ 2) :=
-- proof
  ⟨HampathState, inferInstance, inferInstance, hampathNTM, fun n => n + 2,
    hampathNTM_decides, hampathNTM_runsInTime, hampathNTM_time_bound⟩

end HamiltonianPath

namespace HamiltonianPath

/--
[hampath_in_NP](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
lemma hampath_in_NP
-- imply
  InNP HampathLang :=
-- proof
  ⟨2, hampath_in_NP_aux⟩
/--
For any 3CNF formula `φ`, there exists a `HampathSymbol` (i.e. a graph + source +
target) such that `φ` is satisfiable iff this HAMPATH instance is a YES instance.
This is the existential, abstract form of the classical 3SAT ≤_P HAMPATH reduction.
-/
end HamiltonianPath
/-- Top-level restatement: `HamiltonianPath.HampathLang` is NP-complete. -/


/--
[ThreeSAT.mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
private lemma mk_eq
  {φ : BoolFormula}
-- given
  (h3 : φ.Is3CNF)
  (hsat : φ.Satisfiable) :
-- imply
  φ ∈ ThreeSAT := by
-- proof
  apply NPCompleteness.ThreeSAT.mk h3 hsat

/--
[tseitinAux_soundness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
private lemma tseitinAux_soundness_eq :
-- imply
  ∀ (φ : BoolFormula) (fresh : ℕ) (σ : BoolAssignment), (∀ c ∈ (tseitinAux φ fresh).2.1, c.eval σ = true) → σ (tseitinAux φ fresh).1 = φ.eval σ := by
-- proof
  apply ThreeSATComplete.tseitinAux_soundness

/--
[conjoinClauses_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean)
-/
@[path]
private lemma conjoinClauses_eval_eq :
-- imply
  ∀ (cs : List BoolFormula) (_ : cs ≠ []) (σ : BoolAssignment), (conjoinClauses cs).eval σ = true ↔ ∀ c ∈ cs, c.eval σ = true := by
-- proof
  apply ThreeSATComplete.conjoinClauses_eval


-- created on 2026-10-23
