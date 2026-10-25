import Mathlib
import sympy.Basic
import Def.v1.Atlas.TheoryOfComputation.code.GraphNonIsoIP.Part2
open GraphNonIsoIP InteractiveProofs Probabilistic in
open InteractiveProofs Probabilistic TuringMachine


namespace GraphNonIsoIP

/--
[coin_match_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GraphNonIsoIP.lean)
-/
@[path]
lemma coin_match_le_one
  {g1 g2 : Bool} :
-- imply
  (Finset.univ.filter (fun (coins : Fin 2 → Bool) => ((g1 == coins ⟨0, by omega⟩) && (g2 == coins ⟨1, by omega⟩)) = true)).card ≤ 1 := by
-- proof
  fin_cases g1 <;> fin_cases g2 <;> decide

end GraphNonIsoIP

namespace GraphNonIsoIP

/--
[iso_bar_in_IP](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GraphNonIsoIP.lean)
-/
@[path]
lemma iso_bar_in_IP
  {Γ : Type}
  [DecidableEq Γ]
  [Inhabited Γ]
  {enc : GraphPairEncoding Γ}
  {perm : GraphPermuter Γ enc} :
-- imply
  InIP (ISO_bar enc) := by
-- proof
  refine ⟨Bool, inferInstance, isoBarVerifier perm, isoBarHonestProver perm,
    1, fun _ => 2, 1, fun _ => 2, ?_, ?_, ?_⟩
  ·
    exact ⟨2, 1, by omega, fun n hn => by simp; omega⟩
  ·
    exact ⟨2, 1, by omega, fun n hn => by simp; omega⟩
  ·
    unfold IsInteractiveProofSystem
    constructor
    ·
      intro w hw
      unfold Verifier.acceptProb Verifier.numAccepting
      have hw_not_iso : w ∉ ISO enc := hw
      suffices h : ∀ coins : Fin 2 → Bool,
        runProtocol (isoBarVerifier perm) (isoBarHonestProver perm) w 2 coins 2 = true by
        simp only [Finset.filter_true_of_mem (fun x _ => h x), Finset.card_univ,
          Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
        norm_num
      intro coins
      show runProtocol (isoBarVerifier perm) (isoBarHonestProver perm) w 2 coins 2 = true
      simp only [runProtocol, runRounds, isoBarVerifier, isoBarHonestProver,
        show (2 : ℕ) ≥ 2 from le_refl 2, dite_true,
        List.length_nil, List.length_append, List.length_cons, List.length_singleton,
        List.nil_append, List.cons_append, Nat.reduceAdd,
        show (0 : ℕ) = 0 from rfl, show ¬(2 : ℕ) = 0 from by omega, show (2 : ℕ) = 2 from rfl,
        ite_true, ite_false]
      have hid := perm.identify_correct w hw_not_iso
      set b1 := coins ⟨0, by omega⟩
      set b2 := coins ⟨1, by omega⟩
      have hid1 : perm.identify w (perm.challenge w b1 w) = b1 := hid b1 w
      have hid2 : perm.identify w (perm.challenge w b2 w) = b2 := hid b2 w
      simp only [hid1, hid2]
      cases b1 <;> cases b2 <;> simp [hid _ w]
    ·
      intro w hw P'
      unfold Verifier.acceptProb Verifier.numAccepting
      have hw_iso : w ∈ ISO enc := by
        simp only [ISO_bar, Set.mem_compl_iff] at hw
        exact not_not.mp hw
      have hchallenge_eq : ∀ (b : Bool),
        perm.challenge w b w = perm.challenge w true w := by
        intro b; cases b
        · exact (perm.iso_challenge_eq w hw_iso w).symm
        · rfl
      have heq : ∀ coins : Fin 2 → Bool,
        runProtocol (isoBarVerifier perm) P' w 2 coins 2 =
          let c := perm.challenge w true w
          let r1 := P' w [c]
          let g1 : Bool := !r1.isEmpty
          let r2 := P' w [c, r1, c]
          let g2 : Bool := !r2.isEmpty
          (coins ⟨0, by omega⟩ == g1) && (coins ⟨1, by omega⟩ == g2) := by
        intro coins
        simp only [runProtocol, runRounds, isoBarVerifier,
          show (2 : ℕ) ≥ 2 from le_refl 2, dite_true,
          List.length_nil, List.length_append, List.length_cons, List.length_singleton,
          List.nil_append, List.cons_append, Nat.reduceAdd, ite_true, ite_false, decide_true, decide_false]
        rw [hchallenge_eq (coins ⟨0, by omega⟩)]
        rw [hchallenge_eq (coins ⟨1, by omega⟩)]
        simp only [show ¬(2 : ℕ) = 0 from by omega, ite_false]
      set c := perm.challenge w true w
      set r1 := P' w [c]
      set g1 : Bool := !r1.isEmpty
      set r2 := P' w [c, r1, c]
      set g2 : Bool := !r2.isEmpty
      have hfilter : (Finset.univ.filter (fun coins : Fin 2 → Bool =>
        runProtocol (isoBarVerifier perm) P' w 2 coins 2 = true)) =
        (Finset.univ.filter (fun coins : Fin 2 → Bool =>
          ((coins ⟨0, by omega⟩ == g1) && (coins ⟨1, by omega⟩ == g2)) = true)) := by
        ext coins
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [heq]
      rw [hfilter]
      have hfilter2 : (Finset.univ.filter (fun coins : Fin 2 → Bool =>
        ((coins ⟨0, by omega⟩ == g1) && (coins ⟨1, by omega⟩ == g2)) = true)) =
        (Finset.univ.filter (fun coins : Fin 2 → Bool =>
          ((g1 == coins ⟨0, by omega⟩) && (g2 == coins ⟨1, by omega⟩)) = true)) := by
        congr 1; ext coins
        simp only [Bool.beq_comm]
      rw [hfilter2]
      have hcount := coin_match_le_one g1 g2
      have hle : ((Finset.univ.filter (fun coins : Fin 2 → Bool =>
        ((g1 == coins ⟨0, by omega⟩) && (g2 == coins ⟨1, by omega⟩))
          = true)).card : ℚ) ≤ 1 :=
        Nat.cast_le.mpr hcount
      linarith

end GraphNonIsoIP

/--
[ISO_bar_in_IP](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GraphNonIsoIP.lean)
-/
@[path]
lemma ISO_bar_in_IP
  {Γ : Type}
  [DecidableEq Γ]
  [Inhabited Γ]
  {enc : GraphPairEncoding Γ} :
-- imply
  InIP (ISO_bar enc) :=
-- proof
  GraphNonIsoIP.iso_bar_in_IP enc (GraphNonIsoIP.defaultGraphPermuter enc)


-- created on 2026-10-23
