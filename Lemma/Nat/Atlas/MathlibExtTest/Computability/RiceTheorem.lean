import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Computability.RiceTheorem


/--
[riceTheoremTest_standardNumbering_row](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Computability/RiceTheorem.lean)
-/
@[path]
lemma riceTheoremTest_standardNumbering_row
  {e : ℕ} :
-- imply
  Nat.Partrec (riceTheoremTest_standardNumbering e) :=
-- proof
  Partrec.nat_iff.1 <|
    Nat.Partrec.Code.eval_part.comp (Computable.const _) Computable.id

/--
[riceTheoremTest_standardNumbering_univ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Computability/RiceTheorem.lean)
-/
@[path]
lemma riceTheoremTest_standardNumbering_univ :
-- imply
  Nat.Partrec (Nat.unpaired riceTheoremTest_standardNumbering) := by
-- proof
  apply Partrec₂.unpaired'.2
  change Partrec fun p : ℕ × ℕ =>
    Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code p.1) p.2
  exact Nat.Partrec.Code.eval_part.comp
    ((Computable.ofNat Nat.Partrec.Code).comp Computable.fst) Computable.snd

/--
[riceTheoremTest_standardNumbering_index](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Computability/RiceTheorem.lean)
-/
@[path]
lemma riceTheoremTest_standardNumbering_index
  {f : ℕ →. ℕ}
-- given
  (hf : Nat.Partrec f) :
-- imply
  ∃ e, ∀ n, riceTheoremTest_standardNumbering e n = f n := by
-- proof
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hf
  refine ⟨Encodable.encode c, fun n => ?_⟩
  simp only [riceTheoremTest_standardNumbering, Denumerable.ofNat_encode, hc]

/--
[riceTheoremTest_standardNumbering_smn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Computability/RiceTheorem.lean)
-/
@[path]
lemma riceTheoremTest_standardNumbering_smn
  {g : ℕ → ℕ →. ℕ}
-- given
  (hg : Nat.Partrec (Nat.unpaired g)) :
-- imply
  ∃ s : ℕ → ℕ, Nat.Partrec (fun n => Part.some (s n)) ∧ ∀ e n, riceTheoremTest_standardNumbering (s e) n = g e n := by
-- proof
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hg
  obtain ⟨curry, hcurry, hcurry_spec⟩ := Nat.Partrec.Code.smn
  let s : ℕ → ℕ := fun e => Encodable.encode (curry c e)
  refine ⟨s, ?_, ?_⟩
  · exact Partrec.nat_iff.1 <|
    Computable.encode.comp (hcurry.comp (Computable.const c) Computable.id)
  · intro e n
    simp only [riceTheoremTest_standardNumbering, s, Denumerable.ofNat_encode, hcurry_spec, hc,
      Nat.unpaired, Nat.unpair_pair]


-- created on 2026-10-23
-- updated on 2026-10-28
