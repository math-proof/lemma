import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfComputation.code.SelfReference.Part7
open SelfReference TuringMachine GodelIncompleteness
open TuringMachine


namespace SelfReference

/--
[exists_self_reproducing_tm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean)
-/
@[path]
lemma exists_self_reproducing_tm
  {Γ : Type}
  {F : SelfRefFramework Γ} :
-- imply
  ∃ (M : TMDescription Γ), ∀ (w : List Γ), M.haltsWithOutput w (F.encode M) := by
-- proof
  let B := F.quineB
  have hB_spec := F.quineB_spec
  let descB := F.encode B
  let A := F.printTM descB
  let SELF := F.compose A B
  use SELF
  intro w
  have hA : A.haltsWithOutput w descB := F.printTM_spec descB w
  have hB_run : B.haltsWithOutput descB (F.combineDesc (F.q descB) (F.encode B)) :=
    hB_spec descB
  have hq : F.q descB = F.encode A := rfl
  have henc : F.combineDesc (F.encode A) (F.encode B) = F.encode SELF :=
    (F.encode_compose A B).symm
  rw [hq] at hB_run
  rw [henc] at hB_run
  exact F.compose_spec A B w descB (F.encode SELF) hA hB_run

end SelfReference

namespace TuringMachine

/--
[recursion_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean)
-/
@[path]
lemma recursion_theorem
  {Γ : Type}
  {C : TMCoding Γ}
  {t : C.TMIndex → C.TMIndex}
-- given
  (ht : C.IsComputable t) :
-- imply
  ∃ R : C.TMIndex, C.languageOf R = C.languageOf (t R) := by
-- proof
  let h : C.TMIndex → C.TMIndex := fun x => t (C.smn x x)
  have hh : C.IsComputable h :=
    C.isComputable_comp t (fun x => C.smn x x) ht C.isComputable_smn_diag
  obtain ⟨e₀, he₀⟩ := C.representable h hh
  let R := C.smn e₀ e₀
  refine ⟨R, ?_⟩
  exact he₀ e₀

end TuringMachine

namespace TuringMachine

/--
[fixed_point_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean)
-/
@[path]
lemma fixed_point_theorem
  {C : TMCoding Γ}
  {f : List Γ → List Γ}
-- given
  (_hf : IsComputableFunction f)
  (hf_maps_to_valid : ∀ M : C.TMIndex, ∃ S : C.TMIndex, C.decode (f (C.encode M)) = some S)
  (ht_computable : ∀ (t : C.TMIndex → C.TMIndex), (∀ M, C.decode (f (C.encode M)) = some (t M)) → C.IsComputable t) :
-- imply
  ∃ R : C.TMIndex, ∃ S : C.TMIndex, C.decode (f (C.encode R)) = some S ∧ C.languageOf R = C.languageOf S := by
-- proof
  classical
  let t : C.TMIndex → C.TMIndex := fun M => (hf_maps_to_valid M).choose
  have ht : ∀ M, C.decode (f (C.encode M)) = some (t M) :=
    fun M => (hf_maps_to_valid M).choose_spec
  obtain ⟨R, hR⟩ := recursion_theorem C t (ht_computable t ht)
  exact ⟨R, t R, ht R, hR⟩

end TuringMachine

namespace TuringMachine

/--
[computable_q_is_computable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean)
-/
@[path]
lemma computable_q_is_computable
  {Γ : Type}
  [DecidableEq Γ]
  {Γ : Type}
  {enc : SelfReference.TMEncoding Γ} :
-- imply
  ∃ q : List Γ → List Γ, IsComputableFunction q ∧ ∀ w, ∃ (Pw : SelfReference.TMDescription Γ), q w = enc.encode Pw ∧ ∀ input, Pw.haltsWithOutput input w := by
-- proof
  refine ⟨fun w => enc.encode (enc.printTMDesc w), enc.q_computable, fun w => ?_⟩
  exact ⟨enc.printTMDesc w, rfl, enc.printTMDesc_spec w⟩

end TuringMachine

namespace TuringMachine

/--
[computable_q](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean)
-/
@[path]
lemma computable_q
  {Γ : Type}
  [DecidableEq Γ]
  {blank : Γ}
  {inputAlpha : Set Γ}
-- given
  (h_blank : blank ∉ inputAlpha) :
-- imply
  ∃ q : List Γ → List Γ, IsComputableFunction q ∧ ∀ w, ∃ (Pw : SelfReference.TMDescription Γ), q w = (concreteTMEncoding blank inputAlpha h_blank).encode Pw ∧ ∀ input, Pw.haltsWithOutput input w :=
-- proof
  computable_q_is_computable (concreteTMEncoding blank inputAlpha h_blank)

end TuringMachine

namespace TuringMachine

/--
[exists_minimal_for_language](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean)
-/
@[path]
lemma exists_minimal_for_language
  {Γ : Type}
  {C : TMCoding Γ}
  {M : C.TMIndex} :
-- imply
  ∃ M' : C.TMIndex, C.languageOf M' = C.languageOf M ∧ IsMinimalIndex C M' := by
-- proof
  classical
  have : ∀ k : ℕ, ∀ N : C.TMIndex, (C.encode N).length = k →
    ∃ M' : C.TMIndex, C.languageOf M' = C.languageOf N ∧ IsMinimalIndex C M' := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro N hNk
      by_cases hmin : IsMinimalIndex C N
      · exact ⟨N, rfl, hmin⟩
      ·
        unfold IsMinimalIndex at hmin
        push Not at hmin
        obtain ⟨N', hN'_short, hN'_lang⟩ := hmin
        have hN'_len : (C.encode N').length < k := hNk ▸ hN'_short
        obtain ⟨M', hM'_lang, hM'_min⟩ := ih (C.encode N').length hN'_len N' rfl
        exact ⟨M', hM'_lang.trans hN'_lang, hM'_min⟩
  exact this (C.encode M).length M rfl

end TuringMachine

namespace TuringMachine

/--
[min_tm_has_arbitrarily_long_elements](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean)
-/
@[path]
lemma min_tm_has_arbitrarily_long_elements
  {Γ : Type}
  {C : TMCoding Γ} :
-- imply
  ∀ n : ℕ, ∃ B : C.TMIndex, IsMinimalIndex C B ∧ n ≤ (C.encode B).length := by
-- proof
  intro n
  obtain ⟨M, hM⟩ := C.languages_beyond_length n
  obtain ⟨M', hM'_lang, hM'_min⟩ := exists_minimal_for_language C M
  refine ⟨M', hM'_min, ?_⟩
  by_contra h
  push Not at h
  exact hM M' h (hM'_lang)

end TuringMachine

namespace TuringMachine

/--
[min_tm_arbitrarily_long_strict](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean)
-/
@[path]
lemma min_tm_arbitrarily_long_strict
  {Γ : Type}
  {C : TMCoding Γ} :
-- imply
  ∀ n : ℕ, ∃ B : C.TMIndex, IsMinimalIndex C B ∧ n < (C.encode B).length := by
-- proof
  intro n
  obtain ⟨B, hB_min, hB_len⟩ := min_tm_has_arbitrarily_long_elements C (n + 1)
  exact ⟨B, hB_min, by omega⟩

end TuringMachine

namespace TuringMachine

/--
[MIN_TM_not_recognizable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean)
-/
@[path]
lemma MIN_TM_not_recognizable
  {Γ : Type}
  {C : TMCoding Γ} :
-- imply
  ¬ IsTuringRecognizable (MIN_TM_Coding C) := by
-- proof
  intro hRec
  have h_inf := min_tm_arbitrarily_long_strict C
  classical
  let t : C.TMIndex → C.TMIndex := fun M => (h_inf (C.encode M).length).choose
  have ht_spec : ∀ M, IsMinimalIndex C (t M) ∧
    (C.encode M).length < (C.encode (t M)).length :=
    fun M => (h_inf (C.encode M).length).choose_spec
  have ht_comp : C.IsComputable t :=
    C.recognizable_enumSearch_computable (IsMinimalIndex C) hRec t ht_spec
  obtain ⟨R, hR⟩ := recursion_theorem C t ht_comp
  exact (ht_spec R).1 R (ht_spec R).2 hR
end TuringMachine
namespace TuringMachine
open TuringMachine

end TuringMachine

namespace TuringMachine

/--
[A_TM_not_decidable_via_recursion_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean)
-/
@[path]
lemma A_TM_not_decidable_via_recursion_theorem
  {enc : TMEncoding Γ} :
-- imply
  ¬IsTuringDecidable (A_TM enc) := by
-- proof
  intro ⟨QH, decEqH, H, hDecider, hLang⟩
  have hH_iff : ∀ d : TMDesc Γ,
    @TM.accepts QH Γ decEqH H (enc.encode d) ↔ d.accepts := by
    intro d
    have hLang' : ∀ w, @TM.accepts QH Γ decEqH H w ↔ w ∈ A_TM enc := by
      intro w
      change w ∈ @TM.language QH Γ decEqH H ↔ w ∈ A_TM enc
      rw [hLang]
    rw [hLang' (enc.encode d)]
    constructor
    · rintro ⟨d', henc, hacc⟩
      exact enc.encode_injective henc ▸ hacc
    · intro hacc
      exact ⟨d, rfl, hacc⟩
  let D := @TM.flip QH Γ decEqH H
  have hD : ∀ w, @TM.accepts QH Γ decEqH D w ↔
    ¬ @TM.accepts QH Γ decEqH H w :=
    TM.flip_accepts_iff H hDecider
  obtain ⟨d₀, hSelfRef⟩ := enc.selfRef D
  have hcontra : d₀.accepts ↔ ¬ d₀.accepts := by
    calc d₀.accepts
      ↔ @TM.accepts QH Γ decEqH D (enc.encode d₀) := hSelfRef
      _ ↔ ¬ @TM.accepts QH Γ decEqH H (enc.encode d₀) := hD _
      _ ↔ ¬ d₀.accepts := not_congr (hH_iff d₀)
  by_cases h : d₀.accepts
  · exact hcontra.mp h h
  · exact h (hcontra.mpr h)
end TuringMachine
namespace GodelIncompleteness
open TuringMachine


namespace GodelIncompleteness

/--
[godel_first_incompleteness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean)
-/
@[path]
lemma godel_first_incompleteness
  {Γ : Type}
  {enc : TMEncoding Γ}
  {provable : Set (List Γ)}
-- given
  (h_provable_recognizable : IsTuringRecognizable provable)
  (h_sound : ∀ (d : TMDesc Γ), enc.encode d ∈ provable → ¬d.accepts) :
-- imply
  ∃ (d : TMDesc Γ), ¬d.accepts ∧ enc.encode d ∉ provable := by
-- proof
  obtain ⟨QP, decEqP, P, hP⟩ := h_provable_recognizable
  obtain ⟨d₀, hSelfRef⟩ := enc.selfRef P
  refine ⟨d₀, ?_, ?_⟩
  ·
    intro hAccepts
    have hPAccepts := hSelfRef.mp hAccepts
    have hProvable : enc.encode d₀ ∈ provable := by rw [← hP]; exact hPAccepts
    exact h_sound d₀ hProvable hAccepts
  ·
    intro hProvable
    have hNotAccepts := h_sound d₀ hProvable
    have hPAccepts : @TM.accepts QP Γ decEqP P (enc.encode d₀) := by
      rw [← hP] at hProvable; exact hProvable
    exact hNotAccepts (hSelfRef.mpr hPAccepts)

end GodelIncompleteness

namespace GodelIncompleteness

/--
[true_but_unprovable_statement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean)
-/
@[path]
lemma true_but_unprovable_statement
  {Γ : Type}
  {enc : TMEncoding Γ}
  {provable : Set (List Γ)}
  {QP : Type}
  [DecidableEq QP]
  {P : TM QP Γ}
-- given
  (h_sound : ∀ (d : TMDesc Γ), enc.encode d ∈ provable → ¬d.accepts)
  (hP : P.language = provable) :
-- imply
  ∃ (d : TMDesc Γ), ¬d.accepts ∧ enc.encode d ∉ provable := by
-- proof
  obtain ⟨d₀, hSelfRef⟩ := enc.selfRef P
  refine ⟨d₀, ?_, ?_⟩
  ·
    intro hAccepts
    have hPAccepts := hSelfRef.mp hAccepts
    have hProvable : enc.encode d₀ ∈ provable := by
      rwa [← hP]
    exact h_sound d₀ hProvable hAccepts
  ·
    intro hProvable
    have hNotAccepts := h_sound d₀ hProvable
    have hPAccepts : @TM.accepts QP Γ _ P (enc.encode d₀) := by
      rwa [← hP] at hProvable
    exact hNotAccepts (hSelfRef.mpr hPAccepts)

end GodelIncompleteness

/--
[printTM_invariant_any_input](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean)
-/
@[path]
private lemma printTM_invariant_any_input_eq
  {Γ : Type}
  [DecidableEq Γ]
  {blank : Γ}
  {inputAlpha : Set Γ}
  {w : List Γ}
  {input : List Γ}
  {k : ℕ}
-- given
  (h_blank : blank ∉ inputAlpha)
  (hk : k ≤ w.length) :
-- imply
  ((printTM blank inputAlpha h_blank w).runOnInput input k).state = ⟨k, by omega⟩ ∧ ((printTM blank inputAlpha h_blank w).runOnInput input k).headPos = (k : ℤ) ∧ (∀ (j : ℕ) (hj : j < k), ((printTM blank inputAlpha h_blank w).runOnInput input k).tape (j : ℤ) = w[j]'(by omega)) := by
-- proof
  apply TuringMachine.printTM_invariant_any_input blank inputAlpha h_blank w input k hk

/--
[printTM_haltsWithOutput](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean)
-/
@[path]
private lemma printTM_haltsWithOutput_eq
  {Γ : Type}
  [DecidableEq Γ]
  {blank : Γ}
  {inputAlpha : Set Γ}
  {w input : List Γ}
-- given
  (h_blank : blank ∉ inputAlpha) :
-- imply
  ∃ n : ℕ, (printTM blank inputAlpha h_blank w).isHaltConfig ((printTM blank inputAlpha h_blank w).runOnInput input n) ∧ Config.readTape ((printTM blank inputAlpha h_blank w).runOnInput input n) w.length = w := by
-- proof
  apply TuringMachine.printTM_haltsWithOutput blank inputAlpha h_blank w input


-- created on 2026-10-23
