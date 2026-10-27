import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.CerednikDrinfeld.DrinfeldHolomorphic
import Lemma.Int.P2MUtil

open CerednikDrinfeld.Omega

/--
[CerednikDrinfeld_Omega_restrict_mem_holOn_of_subset](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_Omega_restrict_mem_holOn_of_subset.lean)
-/
@[path]
private lemma main
  [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
  {S T : Set K}
  {f : ↥S → K}
-- given
  (hTS : T ⊆ S)
  (hf : f ∈ holOn K S) :
-- imply
  (fun z : ↥T => f ⟨(z : K), hTS z.2⟩) ∈ holOn K T := by
-- proof
  rw [mem_holOn_iff] at hf ⊢
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  exact ⟨r, fun k z hz => hr k z (hTS hz), ⟨b, fun k z => hb k ⟨(z : K), hTS z.2⟩⟩,
    hlim.comp (fun z : ↥T => (⟨(z : K), hTS z.2⟩ : ↥S))⟩


-- created on 2026-10-23
