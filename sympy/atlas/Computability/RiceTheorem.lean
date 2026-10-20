/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Computability/RiceTheorem.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Computability.Partrec

/-!
# Rice's theorem for acceptable numberings

This file proves Kleene's recursion theorem and Rice's theorem for an abstract acceptable
numbering of the partial computable functions from `ℕ` to `ℕ`.
-/

namespace MetaMathlibExt

private theorem riceTheorem_partrec₂ {φ : ℕ → ℕ →. ℕ}
    (huniv : Nat.Partrec (fun p => φ (Nat.unpair p).1 (Nat.unpair p).2)) : Partrec₂ φ :=
  Partrec₂.unpaired'.1 huniv

private theorem riceTheorem_diagonal {φ : ℕ → ℕ →. ℕ} (hφ : Partrec₂ φ) :
    Partrec₂ fun x n => (φ x x).bind fun y => φ y n :=
  (hφ.comp Computable.fst Computable.fst).bind
    (hφ.comp Computable.snd (Computable.snd.comp Computable.fst)).to₂

/-- Rogers's fixed-point theorem for an acceptable numbering of the partial computable
functions `ℕ →. ℕ`. -/
theorem acceptableNumbering_fixed_point (φ : ℕ → ℕ →. ℕ)
    (huniv : Nat.Partrec (fun p => φ (Nat.unpair p).1 (Nat.unpair p).2))
    (hidx : ∀ f : ℕ →. ℕ, Nat.Partrec f → ∃ e, ∀ n, φ e n = f n)
    (hsmn : ∀ g : ℕ → ℕ →. ℕ,
      Nat.Partrec (fun p => g (Nat.unpair p).1 (Nat.unpair p).2) →
      ∃ s : ℕ → ℕ, Nat.Partrec (fun n => Part.some (s n)) ∧
        ∀ e n, φ (s e) n = g e n)
    {h : ℕ → ℕ} (hh : Computable h) : ∃ e, ∀ n, φ e n = φ (h e) n := by
  have hφ := riceTheorem_partrec₂ huniv
  have hdiag := riceTheorem_diagonal hφ
  obtain ⟨s, hs, hs_spec⟩ := hsmn _ (Partrec₂.unpaired'.2 hdiag)
  have hs_comp : Computable s := Partrec.nat_iff.2 hs
  have htotal : Nat.Partrec (fun x => Part.some (h (s x))) :=
    Partrec.nat_iff.1 (hh.comp hs_comp)
  obtain ⟨v, hv⟩ := hidx _ htotal
  refine ⟨s v, fun n => ?_⟩
  rw [hs_spec v n, hv v, Part.bind_some]

private theorem riceTheorem_selector (dec : ℕ → ℕ) (hdec : Computable dec) (a b : ℕ) :
    Computable fun x => cond (dec x == 1) b a :=
  Computable.cond (Primrec.beq.to_comp.comp hdec (Computable.const 1))
    (Computable.const b) (Computable.const a)

/-- Rice's theorem (rice-s1): any nontrivial semantic index set for an acceptable
numbering of partial computable functions is undecidable. Codes are `ℕ` via the
acceptable enumeration `φ` with computable universal evaluation and the s-m-n
property; extensional equivalence is `∀ n, φ a n = φ b n`; nontriviality means the
index set is both inhabited and non-universal; undecidability is nonexistence
of a computable decider.
Source: H. G. Rice, *Classes of recursively enumerable sets and their decision problems*,
Transactions of the American Mathematical Society 74(2) (1953), 358-366.

Proves `Wanted` entry `rice_theorem`.

Proof: The standard argument first derives Kleene's recursion theorem for the acceptable
numbering, then diagonalizes a putative decider, following Rice (1953), Rogers §11.2, and
Soare II.3.1.
-/
theorem rice_theorem : ∀ (φ : ℕ → ℕ →. ℕ),
    (∀ e, Nat.Partrec (φ e)) →
    Nat.Partrec (fun p => φ (Nat.unpair p).1 (Nat.unpair p).2) →
    (∀ f : ℕ →. ℕ, Nat.Partrec f → ∃ e, ∀ n, φ e n = f n) →
    (∀ g : ℕ → ℕ →. ℕ,
      Nat.Partrec (fun p => g (Nat.unpair p).1 (Nat.unpair p).2) →
      ∃ s : ℕ → ℕ, Nat.Partrec (fun n => Part.some (s n)) ∧
        ∀ e n, φ (s e) n = g e n) →
    ∀ (C : Set ℕ),
      (∀ a b, (∀ n, φ a n = φ b n) → (a ∈ C ↔ b ∈ C)) →
      (∃ a, a ∈ C) → (∃ b, b ∉ C) →
      ¬ ∃ dec : ℕ → ℕ, Nat.Partrec (fun n => Part.some (dec n)) ∧
        ∀ e, (e ∈ C ↔ dec e = 1) ∧ (e ∉ C ↔ dec e = 0) := by
  intro φ hrow huniv hidx hsmn C hext ⟨a, ha⟩ ⟨b, hb⟩
  rintro ⟨dec, hdec, hdecides⟩
  have hdec_comp : Computable dec := Partrec.nat_iff.2 hdec
  let sel : ℕ → ℕ := fun x => cond (dec x == 1) b a
  have hsel : Computable sel := by
    simpa [sel] using riceTheorem_selector dec hdec_comp a b
  let g : ℕ → ℕ →. ℕ := fun x n => φ (sel x) n
  have hg : Partrec₂ g := by
    change Partrec fun p : ℕ × ℕ => φ (sel p.1) p.2
    exact (riceTheorem_partrec₂ huniv).comp (hsel.comp Computable.fst) Computable.snd
  obtain ⟨h, hh, hh_spec⟩ := hsmn g (Partrec₂.unpaired'.2 hg)
  have hh_comp : Computable h := Partrec.nat_iff.2 hh
  obtain ⟨e, he⟩ :=
    acceptableNumbering_fixed_point φ huniv hidx hsmn hh_comp
  have he_sel : ∀ n, φ e n = φ (sel e) n := fun n => (he n).trans (hh_spec e n)
  by_cases heC : e ∈ C
  · have hde : dec e = 1 := (hdecides e).1.mp heC
    have heb : ∀ n, φ e n = φ b n := by
      intro n
      simpa [sel, hde] using he_sel n
    exact hb ((hext e b heb).mp heC)
  · have hde : dec e = 0 := (hdecides e).2.mp heC
    have hea : ∀ n, φ e n = φ a n := by
      intro n
      simpa [sel, hde] using he_sel n
    exact heC ((hext e a hea).mpr ha)

end MetaMathlibExt
