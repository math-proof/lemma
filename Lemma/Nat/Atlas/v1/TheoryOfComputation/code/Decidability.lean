import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part13
open TuringMachine in Classical Decidability LBADecidability


namespace Decidability

/--
[set_not_countable_of_countable_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma set_not_countable_of_countable_infinite
  [Countable α]
  [Infinite α] :
-- imply
  ¬ Countable (Set α) := by
-- proof
  intro h
  obtain ⟨f, hf⟩ := exists_injective_nat (Set α)
  haveI : Denumerable α := Denumerable.mk' (nonempty_equiv_of_countable.some)
  let e := (Denumerable.eqv α).symm
  exact Function.cantor_injective (e ∘ f) (e.injective.comp hf)

end Decidability

namespace Decidability

/--
[languages_uncountable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma languages_uncountable
  {Alphabet : Type*}
  [Nonempty Alphabet]
  [Countable Alphabet] :
-- imply
  ¬ Countable (Language Alphabet) :=
-- proof
  set_not_countable_of_countable_infinite
end Decidability
open TuringMachine


namespace TuringMachine

/--
[TM.run_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma TM.run_add
  {Γ : Type}
  {Q Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c : Config Q Γ}
  {m n : ℕ} :
-- imply
  M.run c (m + n) = M.run (M.run c m) n := by
-- proof
  induction n with
  | zero => simp [TM.run]
  | succ n ih =>
    show M.step (M.run c (m + n)) = M.step (M.run (M.run c m) n)
    rw [ih]

end TuringMachine

namespace TuringMachine

/--
[TM.halts_of_accepts](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma TM.halts_of_accepts
  {Γ : Type}
  {Q : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {w : List Γ}
-- given
  (h : M.accepts w) :
-- imply
  M.halts w := by
-- proof
  obtain ⟨n, hacc⟩ := h
  exact ⟨n, Or.inl hacc⟩

end TuringMachine

namespace TuringMachine

/--
[A_TM_subset_HALT_TM](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma A_TM_subset_HALT_TM
  {Γ : Type}
  {enc : TMEncoding Γ} :
-- imply
  A_TM enc ⊆ HALT_TM enc := by
-- proof
  intro s ⟨d, henc, hacc⟩
  refine ⟨d, henc, ?_⟩
  obtain ⟨n, hacc'⟩ := hacc
  exact ⟨n, Or.inl hacc'⟩

end TuringMachine

/--
[TuringMachine.TM.flip_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma TuringMachine.TM.flip_step
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {H : TuringMachine.TM Q Γ}
  {c : TuringMachine.Config Q Γ} :
-- imply
  (H.flip Γ).step c = H.step c := by
-- proof
  simp only [TuringMachine.TM.step, TuringMachine.TM.flip]
  split_ifs with h1 h2 h2
  · rfl
  ·
    exfalso; exact h2 (h1.elim Or.inr Or.inl)
  ·
    exfalso; exact h1 (h2.elim Or.inr Or.inl)
  · rfl

/--
[TuringMachine.TM.flip_run](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma TuringMachine.TM.flip_run
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {H : TuringMachine.TM Q Γ}
  {c : TuringMachine.Config Q Γ}
  {n : ℕ} :
-- imply
  (H.flip Γ).run c n = H.run c n := by
-- proof
  induction n with
  | zero => rfl
  | succ n ih => simp only [TuringMachine.TM.run, ih, H.flip_step]

/--
[TuringMachine.TM.flip_accepts_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma TuringMachine.TM.flip_accepts_iff
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {H : TuringMachine.TM Q Γ}
  {w : List Γ}
-- given
  (hH : H.isDecider) :
-- imply
  (H.flip Γ).accepts w ↔ ¬ H.accepts w := by
-- proof
  have hrun_add : ∀ (c : TuringMachine.Config Q Γ) (a b : ℕ),
    H.run (H.run c a) b = H.run c (a + b) := by
    intro c a b; induction b with
    | zero => rfl
    | succ b ih =>
      change H.step (H.run (H.run c a) b) = _; rw [ih]; rfl
  have hrun_eq : ∀ n, (H.flip Γ).runOnInput w n = H.runOnInput w n := by
    intro n
    show (H.flip Γ).run ((H.flip Γ).initConfig w) n = H.run (H.initConfig w) n
    have hinit : (H.flip Γ).initConfig w = H.initConfig w := by
      simp [TuringMachine.TM.initConfig, TuringMachine.TM.flip]
    rw [hinit, H.flip_run]
  have h_eq : (H.flip Γ).accepts w ↔ H.rejects w := by
    constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
    · change (H.runOnInput w n).state = H.qReject
      change ((H.flip Γ).runOnInput w n).state = (H.flip Γ).qAccept at hn
      rwa [show (H.flip Γ).runOnInput w n = H.runOnInput w n from hrun_eq n,
        show (H.flip Γ).qAccept = H.qReject from rfl] at hn
    · change ((H.flip Γ).runOnInput w n).state = (H.flip Γ).qAccept
      rw [show (H.flip Γ).runOnInput w n = H.runOnInput w n from hrun_eq n,
        show (H.flip Γ).qAccept = H.qReject from rfl]
      exact hn
  rw [h_eq]
  constructor
  · rintro ⟨n, href⟩ ⟨m, hacc⟩
    have reject_persists : ∀ k,
      (H.run (H.run (H.initConfig w) n) k).state = H.qReject := by
      intro k
      induction k with
      | zero => exact href
      | succ k ihk =>
        show (H.step (H.run (H.run (H.initConfig w) n) k)).state = H.qReject
        rw [H.step_of_halt _ (Or.inr ihk)]; exact ihk
    have hstable2 := H.accepts_stable (H.runOnInput w m) n hacc
    simp only [TuringMachine.TM.runOnInput] at hstable2
    rw [hrun_add, show m + n = n + m from Nat.add_comm m n] at hstable2
    have hrej := reject_persists m
    rw [hrun_add] at hrej
    exact H.qReject_ne_qAccept (hrej.symm.trans hstable2)
  · intro hna
    obtain ⟨n, hn⟩ := hH w
    obtain hacc | href := hn
    · exact absurd ⟨n, hacc⟩ hna
    · exact ⟨n, href⟩

/--
[TuringMachine.A_TM_not_decidable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma TuringMachine.A_TM_not_decidable
  {Γ : Type}
  {enc : TuringMachine.TMEncoding Γ} :
-- imply
  ¬TuringMachine.IsTuringDecidable (TuringMachine.A_TM enc) := by
-- proof
  intro ⟨QH, decEqH, H, hDecider, hLang⟩
  have hH_iff : ∀ d : TuringMachine.TMDesc Γ,
    @TuringMachine.TM.accepts QH Γ decEqH H (enc.encode d) ↔ d.accepts := by
    intro d
    have hLang' : ∀ w, @TuringMachine.TM.accepts QH Γ decEqH H w ↔
      w ∈ TuringMachine.A_TM enc := by
      intro w
      change w ∈ @TuringMachine.TM.language QH Γ decEqH H ↔ w ∈ TuringMachine.A_TM enc
      rw [hLang]
    rw [hLang' (enc.encode d)]
    constructor
    · rintro ⟨d', henc, hacc⟩
      have := enc.encode_injective henc
      subst this
      exact hacc
    · intro hacc
      exact ⟨d, rfl, hacc⟩
  let D := @TuringMachine.TM.flip QH Γ decEqH H
  have hD : ∀ w, @TuringMachine.TM.accepts QH Γ decEqH D w ↔
    ¬ @TuringMachine.TM.accepts QH Γ decEqH H w :=
    TuringMachine.TM.flip_accepts_iff H hDecider
  obtain ⟨d₀, hSelfRef⟩ := enc.selfRef D
  have hcontra : d₀.accepts ↔ ¬ d₀.accepts := by
    calc d₀.accepts
      ↔ @TuringMachine.TM.accepts QH Γ decEqH D (enc.encode d₀) := hSelfRef
      _ ↔ ¬ @TuringMachine.TM.accepts QH Γ decEqH H (enc.encode d₀) := hD _
      _ ↔ ¬ d₀.accepts := not_congr (hH_iff d₀)
  by_cases h : d₀.accepts
  · exact hcontra.mp h h
  · exact h (hcontra.mpr h)

/--
[TuringMachine.A_TM_decidable_of_HALT_TM_decidable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma TuringMachine.A_TM_decidable_of_HALT_TM_decidable
  {Γ : Type}
  {enc : TuringMachine.TMEncoding Γ}
-- given
  (hHalt : TuringMachine.IsTuringDecidable (TuringMachine.HALT_TM enc)) :
-- imply
  TuringMachine.IsTuringDecidable (TuringMachine.A_TM enc) := by
-- proof
  obtain ⟨QR, decEqR, R, hR_dec, hR_lang⟩ := hHalt
  obtain ⟨QU, decEqU, U, hU_halts, hU_accepts, _⟩ := enc.universalSim
  have hR_iff : ∀ d : TuringMachine.TMDesc Γ,
    @TuringMachine.TM.accepts QR Γ decEqR R (enc.encode d) ↔ d.halts := by
    intro d
    have : ∀ w, @TuringMachine.TM.accepts QR Γ decEqR R w ↔
      w ∈ TuringMachine.HALT_TM enc := by
      intro w
      change w ∈ @TuringMachine.TM.language QR Γ decEqR R ↔ w ∈ TuringMachine.HALT_TM enc
      rw [hR_lang]
    rw [this]
    exact ⟨fun ⟨d', henc, hhalts⟩ => enc.encode_injective henc ▸ hhalts,
      fun hhalts => ⟨d, rfl, hhalts⟩⟩
  have hU_halts_when_R_accepts : ∀ w,
    @TuringMachine.TM.accepts QR Γ decEqR R w →
    @TuringMachine.TM.halts QU Γ decEqU U w := by
    intro w hRw
    have hw_in_halt : w ∈ TuringMachine.HALT_TM enc := by
      have : w ∈ @TuringMachine.TM.language QR Γ decEqR R := hRw
      rwa [hR_lang] at this
    obtain ⟨d, henc, hd_halts⟩ := hw_in_halt
    rw [← henc]
    exact hU_halts d hd_halts
  obtain ⟨QS, decEqS, S, hS_dec, hS_accepts⟩ :=
    enc.sequentialComposition R U hR_dec hU_halts_when_R_accepts
  exact ⟨QS, decEqS, S, hS_dec, by
    ext w
    simp only [TuringMachine.TM.language, Set.mem_setOf_eq]
    rw [hS_accepts w]
    constructor
    ·
      rintro ⟨hRw, hUw⟩
      have hw_halt : w ∈ TuringMachine.HALT_TM enc := by
        have : w ∈ @TuringMachine.TM.language QR Γ decEqR R := hRw
        rwa [hR_lang] at this
      obtain ⟨d, henc, hd_halts⟩ := hw_halt
      rw [TuringMachine.A_TM]
      exact ⟨d, henc, (hU_accepts d hd_halts).mp (henc ▸ hUw)⟩
    ·
      rintro ⟨d, henc, hd_acc⟩
      constructor
      ·
        rw [← henc]
        have hd_halts : d.halts := by
          have hd_in_ATM : enc.encode d ∈ TuringMachine.A_TM enc := ⟨d, rfl, hd_acc⟩
          have hd_in_HALT := TuringMachine.A_TM_subset_HALT_TM enc hd_in_ATM
          obtain ⟨d', henc', hd'_halts⟩ := hd_in_HALT
          exact enc.encode_injective henc' ▸ hd'_halts
        exact (hR_iff d).mpr hd_halts
      ·
        rw [← henc]
        have hd_halts : d.halts := by
          have hd_in_ATM : enc.encode d ∈ TuringMachine.A_TM enc := ⟨d, rfl, hd_acc⟩
          have hd_in_HALT := TuringMachine.A_TM_subset_HALT_TM enc hd_in_ATM
          obtain ⟨d', henc', hd'_halts⟩ := hd_in_HALT
          exact enc.encode_injective henc' ▸ hd'_halts
        exact (hU_accepts d hd_halts).mpr hd_acc⟩

namespace TuringMachine

/--
[HALT_TM_not_decidable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma HALT_TM_not_decidable
  {Γ : Type}
  {enc : TMEncoding Γ} :
-- imply
  ¬IsTuringDecidable (HALT_TM enc) := by
-- proof
  intro hHalt
  exact A_TM_not_decidable enc (A_TM_decidable_of_HALT_TM_decidable enc hHalt)
end TuringMachine
namespace Decidability
open TuringMachine


namespace Decidability

/--
[TM.language_eq_of_same_data](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma TM.language_eq_of_same_data
  {Q Γ : Type}
  [DecidableEq Q]
  {M₁ M₂ : TM Q Γ}
-- given
  (hblank : M₁.blank = M₂.blank)
  (hδ : M₁.δ = M₂.δ)
  (hq₀ : M₁.q₀ = M₂.q₀)
  (hqA : M₁.qAccept = M₂.qAccept)
  (hqR : M₁.qReject = M₂.qReject) :
-- imply
  M₁.language = M₂.language := by
-- proof
  have hstep : ∀ c, M₁.step c = M₂.step c := fun c => by
    simp only [TM.step, hδ, hqA, hqR]
  have hrun : ∀ c k, M₁.run c k = M₂.run c k := by
    intro c k; induction k with
    | zero => rfl
    | succ k ih => simp only [TM.run, ih, hstep]
  ext w
  simp only [TM.language, Set.mem_setOf_eq, TM.accepts, TM.isAcceptConfig,
    TM.runOnInput, hqA, hblank, hq₀, TM.initConfig, hrun]

end Decidability

namespace Decidability

/--
[language_in_range_tmDescToLang](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma language_in_range_tmDescToLang
  {Γ : Type}
  [Fintype Γ]
  [DecidableEq Γ]
  {n : ℕ}
  {M : TM (Fin n) Γ} :
-- imply
  M.language ∈ Set.range (tmDescToLang Γ) := by
-- proof
  refine ⟨⟨n, M.blank, M.δ, M.q₀, M.qAccept, M.qReject⟩, ?_⟩
  simp only [tmDescToLang, dif_pos M.qReject_ne_qAccept]
  exact TM.language_eq_of_same_data _ _ rfl rfl rfl rfl rfl

end Decidability

namespace Decidability

/--
[exists_undecidable_language](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma exists_undecidable_language
  {Γ : Type}
  [Fintype Γ]
  [DecidableEq Γ]
  [Nonempty Γ] :
-- imply
  ∃ L : Set (List Γ), ¬ IsTuringDecidableFinite L := by
-- proof
  by_contra hall
  push Not at hall
  have hsurj : Function.Surjective (tmDescToLang Γ) := by
    intro L
    obtain ⟨n, M, _, hL⟩ := hall L
    obtain ⟨enc, henc⟩ := language_in_range_tmDescToLang M
    exact ⟨enc, by rw [henc, hL]⟩
  have hcount : Countable (Set (List Γ)) := hsurj.countable
  exact set_not_countable_of_countable_infinite hcount

end Decidability

namespace Decidability

/--
[exists_undecidable_language'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma exists_undecidable_language'
  {Γ : Type}
  {enc : TMEncoding Γ} :
-- imply
  ∃ A : Set (List Γ), ¬ IsTuringDecidable A :=
-- proof
  ⟨A_TM enc, A_TM_not_decidable enc⟩

end Decidability

namespace Decidability

/--
[some_language_not_decidable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma some_language_not_decidable
  {Γ : Type}
  [Fintype Γ]
  [DecidableEq Γ]
  [Nonempty Γ] :
-- imply
  ∃ L : Set (List Γ), ¬ IsTuringDecidableFinite L :=
-- proof
  exists_undecidable_language Γ
end Decidability
namespace PostCorrespondence

end Decidability

namespace LBADecidability

/--
[lba_tape_outside_unchanged](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma lba_tape_outside_unchanged
  {Γ : Type}
  {Q Γ : Type}
  [DecidableEq Q]
  {B : LBA Q Γ}
  {w : List Γ}
  {n : ℕ}
  {i : ℤ}
-- given
  (hi : i < 0 ∨ ↑(max 1 w.length) ≤ i) :
-- imply
  (B.toTM.runOnInput w n).tape i = (B.toTM.initConfig w).tape i := by
-- proof
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [TM.runOnInput, TM.run] at *
    rw [TM.step]
    split_ifs with hhalt
    · exact ih
    · simp only
      have hbnd := B.head_bounded w n
      simp only [TM.runOnInput] at hbnd
      have hne : i ≠ (B.toTM.run (B.toTM.initConfig w) n).headPos := by
        obtain hi | hi <;> omega := hi
      simp only [Function.update, dif_neg hne]
      exact ih

end LBADecidability

namespace LBADecidability

/--
[lba_configs_eq_of_bounded_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma lba_configs_eq_of_bounded_eq
  {Γ : Type}
  {Q Γ : Type}
  [DecidableEq Q]
  {B : LBA Q Γ}
  {w : List Γ}
  {n₁ n₂ : ℕ}
-- given
  (h : extractBoundedConfig (max 1 w.length) (B.toTM.runOnInput w n₁) (B.head_bounded w n₁).1 (B.head_bounded w n₁).2 = extractBoundedConfig (max 1 w.length) (B.toTM.runOnInput w n₂) (B.head_bounded w n₂).1 (B.head_bounded w n₂).2) :
-- imply
  B.toTM.runOnInput w n₁ = B.toTM.runOnInput w n₂ := by
-- proof
  simp only [extractBoundedConfig, BoundedConfig, Prod.mk.injEq] at h
  obtain ⟨hstate, hhead_fin, htape⟩ := h
  have hhead : (B.toTM.runOnInput w n₁).headPos =
    (B.toTM.runOnInput w n₂).headPos := by
    simp only [Fin.mk.injEq] at hhead_fin
    have h1 := (B.head_bounded w n₁).1
    have h2 := (B.head_bounded w n₂).1
    omega
  have htape_eq : (B.toTM.runOnInput w n₁).tape =
    (B.toTM.runOnInput w n₂).tape := by
    funext i
    by_cases hrange : 0 ≤ i ∧ i < ↑(max 1 w.length)
    · have := congr_fun htape ⟨i.toNat, by omega⟩
      simp only at this
      convert this using 1 <;> simp [Int.toNat_of_nonneg hrange.1]
    · push Not at hrange
      have hi : i < 0 ∨ ↑(max 1 w.length) ≤ i := by
        by_cases h0 : 0 ≤ i
        · exact Or.inr (hrange h0)
        · exact Or.inl (by omega)
      rw [lba_tape_outside_unchanged B w n₁ i hi,
        lba_tape_outside_unchanged B w n₂ i hi]
  exact Config.mk.injEq _ _ _ _ _ _ |>.mpr ⟨hstate, hhead, htape_eq⟩

end LBADecidability

/--
[A_TM_recognizable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma A_TM_recognizable
  {Γ : Type}
  {enc : TMEncoding Γ} :
-- imply
  IsTuringRecognizable (A_TM enc) := by
-- proof
  obtain ⟨QU, hQU, U, _hU_halts, hU_accepts, hU_valid⟩ := enc.universalSim
  refine ⟨QU, hQU, U, ?_⟩
  ext s
  simp only [TM.language, Set.mem_setOf_eq, A_TM]
  constructor
  ·
    exact hU_valid s
  ·
    rintro ⟨d, rfl, hd_acc⟩
    have hd_halts : d.halts := @TM.halts_of_accepts Γ d.Q d.decEq d.tm d.input hd_acc
    exact (hU_accepts d hd_halts).mpr hd_acc
namespace TuringMachine
/-- **Corollary (Sipser Lecture 8).** The complement `(A_TM)ᶜ` is *not* Turing-recognizable.
For if both `A_TM` and its complement were recognizable, then by the previous theorem `A_TM`
would be decidable, contradicting the diagonal argument. -/
end TuringMachine
open TuringMachine in
/-- Restatement of the previous corollary in the root namespace: `(A_TM)ᶜ` is
T-unrecognizable. -/
namespace AllCFG
open TuringMachine

/--
[TuringMachine.isTuringDecidable_of_mappingReducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean)
-/
@[path]
lemma TuringMachine.isTuringDecidable_of_mappingReducible
  {Γ : Type}
  {enc : TuringMachine.TMEncoding Γ}
  {A B : Set (List Γ)}
-- given
  (hAB : TuringMachine.MappingReducible A B)
  (hB : TuringMachine.IsTuringDecidable B) :
-- imply
  TuringMachine.IsTuringDecidable A := by
-- proof
  obtain ⟨f, hf_comp, hf_red⟩ := hAB
  obtain ⟨Q_B, decEq_B, M_B, hDec_B, hLang_B⟩ := hB
  obtain ⟨Q_S, decEq_S, S, hDec_S, hAcc_S⟩ := enc.transducerComposition f hf_comp M_B hDec_B
  exact ⟨Q_S, decEq_S, S, hDec_S, by
    ext w
    simp only [TuringMachine.TM.language, Set.mem_setOf_eq]
    rw [hAcc_S w]
    constructor
    · intro hacc
      have : f w ∈ @TuringMachine.TM.language Q_B Γ decEq_B M_B := hacc
      rw [hLang_B] at this
      exact (hf_red w).mpr this
    · intro hw
      have : f w ∈ B := (hf_red w).mp hw
      rw [← hLang_B] at this
      exact this⟩
open Classical in
/-- **Sipser's PCP construction.** There is a map `pcpFor` from TM descriptions to PCP
instances such that the constructed instance has a match iff the TM accepts its input, and the
overall input-to-encoding map is TM-computable. This is the technical heart of the reduction
`A_TM ≤ₘ PCP`. -/
namespace PostCorrespondence
/-- **Theorem (Sipser Lecture 10).** The Post Correspondence Problem
`PCP = {⟨P⟩ | P has a match}` is undecidable, by reduction from `A_TM`. -/
end PostCorrespondence


-- created on 2026-10-23
-- updated on 2026-10-28
