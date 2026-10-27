import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.DegreeFormula
open Ideal Module


/--
[DegreeFormula.sum_sub_ones](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeFormula.lean)
-/
@[path]
lemma DegreeFormula.sum_sub_ones
  {s : Finset ι}
  {f : ι → ℕ}
-- given
  (hf : ∀ x ∈ s, 1 ≤ f x) :
-- imply
  s.sum (fun x => f x - 1) = s.sum f - s.card := by
-- proof
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp only [Finset.sum_cons, Finset.card_cons]
    have ha : 1 ≤ f a := hf a (Finset.mem_cons_self a s)
    have hs : ∀ x ∈ s, 1 ≤ f x := fun x hx => hf x (Finset.mem_cons.mpr (Or.inr hx))
    rw [ih hs]
    have hle : s.card ≤ s.sum f := by
      calc s.card = s.sum (fun _ => 1) := by simp
      _ ≤ s.sum f := Finset.sum_le_sum (fun x hx => hs x hx)
    have h1 : f a - 1 + (s.sum f - s.card) = f a + s.sum f - s.card - 1 := by omega
    have h2 : f a + s.sum f - (s.card + 1) = f a + s.sum f - s.card - 1 := by omega
    linarith

/--
[cor27_fundamental_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeFormula.lean)
-/
@[path]
lemma cor27_fundamental_identity
  {K : Type*}
  {L : Type*}
  [CommRing A]
  [CommRing B]
  [Field K]
  [Field L]
  [IsDomain A]
  [IsDomain B]
  [IsDedekindDomain A]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Algebra A K]
  [IsFractionRing A K]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra K L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  {𝔭 : Ideal A}
  [h𝔭p : 𝔭.IsPrime]
-- given
  (h𝔭 : 𝔭 ≠ ⊥) :
-- imply
  (primesOverFinset 𝔭 B).sum (fun 𝔔 => 𝔭.ramificationIdx 𝔔 * 𝔭.inertiaDeg 𝔔) = Module.finrank K L := by
-- proof
  haveI : 𝔭.IsMaximal := h𝔭p.isMaximal h𝔭
  exact Ideal.sum_ramification_inertia B K L h𝔭

/--
[cor27_ramification_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeFormula.lean)
-/
@[path]
lemma cor27_ramification_formula
  {K : Type*}
  {L : Type*}
  [CommRing A]
  [CommRing B]
  [Field K]
  [Field L]
  [IsDomain A]
  [IsDomain B]
  [IsDedekindDomain A]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  [Algebra A K]
  [IsFractionRing A K]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra K L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  {𝔭 : Ideal A}
  [h𝔭p : 𝔭.IsPrime]
-- given
  (h𝔭 : 𝔭 ≠ ⊥)
  (hf : ∀ 𝔔 ∈ primesOverFinset 𝔭 B, 𝔭.inertiaDeg 𝔔 = 1) :
-- imply
  (primesOverFinset 𝔭 B).sum (fun 𝔔 => 𝔭.ramificationIdx 𝔔 - 1) = Module.finrank K L - (primesOverFinset 𝔭 B).card := by
-- proof
  haveI : 𝔭.IsMaximal := h𝔭p.isMaximal h𝔭
  have hfund := Ideal.sum_ramification_inertia B K L h𝔭
  have hsimp : ∀ 𝔔 ∈ primesOverFinset 𝔭 B,
    𝔭.ramificationIdx 𝔔 * 𝔭.inertiaDeg 𝔔 = 𝔭.ramificationIdx 𝔔 := by
    intro 𝔔 h𝔔; rw [hf 𝔔 h𝔔, Nat.mul_one]
  rw [Finset.sum_congr rfl hsimp] at hfund
  rw [DegreeFormula.sum_sub_ones]
  · omega
  · intro 𝔔 h𝔔
    have hmap : Ideal.map (algebraMap A B) 𝔭 ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot h𝔭
    have h𝔔mem := (mem_primesOverFinset_iff h𝔭 B).mp h𝔔
    have hle : Ideal.map (algebraMap A B) 𝔭 ≤ 𝔔 := by
      rw [Ideal.map_le_iff_le_comap]
      exact h𝔔mem.2.over ▸ le_refl _
    exact Nat.one_le_iff_ne_zero.mpr
      (IsDedekindDomain.ramificationIdx_ne_zero hmap h𝔔mem.1 hle)


-- created on 2026-10-23
