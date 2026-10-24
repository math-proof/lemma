import Mathlib
import Lemma.Definitions.Def_LocalLanglands_HeckeCosetLocal
import Lemma.Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option autoImplicit false

open scoped Pointwise ENNReal
open MulAction MeasureTheory

namespace HeckeIntegralSeam

section Padic

open LocalGL2

variable (p : ℕ) [hp : Fact p.Prime]

theorem algebraMap_natCast_p_ne_zero : algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) ≠ 0 := by
  intro h
  have hp0 : (p : ℤ_[p]) = 0 := IsFractionRing.injective ℤ_[p] ℚ_[p] (by rw [h, map_zero])
  exact hp.out.ne_zero (by exact_mod_cast hp0)

noncomputable abbrev padicDiagP : GL (Fin 2) ℚ_[p] :=
  diagPi (p : ℤ_[p]) (algebraMap_natCast_p_ne_zero p)

theorem exists_zmod_natCast_val_sub_dvd (b : ℤ_[p]) :
    ∃ c : ZMod p, (p : ℤ_[p]) ∣ (((ZMod.val c : ℕ) : ℤ_[p]) - b) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine ⟨((PadicInt.zmodRepr b : ℕ) : ZMod p), ?_⟩
  rw [ZMod.val_cast_of_lt (PadicInt.zmodRepr_lt_p b)]
  have hmem := PadicInt.sub_zmodRepr_mem b
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
  have hneg := dvd_neg.mpr hmem
  rwa [neg_sub] at hneg

theorem zmod_eq_of_dvd_natCast_val_sub {c c' : ZMod p}
    (h : (p : ℤ_[p]) ∣ (((ZMod.val c' : ℕ) : ℤ_[p]) - ((ZMod.val c : ℕ) : ℤ_[p]))) : c = c' := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hker : (((ZMod.val c' : ℕ) : ℤ_[p]) - ((ZMod.val c : ℕ) : ℤ_[p]))
      ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    exact h
  rw [RingHom.mem_ker, map_sub, sub_eq_zero, map_natCast, map_natCast] at hker
  have h1 : ((ZMod.val c' : ℕ) : ZMod p) = c' := ZMod.natCast_rightInverse c'
  have h2 : ((ZMod.val c : ℕ) : ZMod p) = c := ZMod.natCast_rightInverse c
  rw [h1, h2] at hker
  exact hker.symm

instance finite_padicInt_quotient_span_p : Finite (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine Finite.of_surjective
    (fun c : ZMod p => Ideal.Quotient.mk _ ((ZMod.val c : ℕ) : ℤ_[p])) fun b => ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨c, hc⟩ := exists_zmod_natCast_val_sub_dvd p b
  exact ⟨c, by rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]; exact hc⟩

theorem finite_image_mulSet_padic :
    (QuotientGroup.mk ''
        ((integralSubgroup ℤ_[p] ℚ_[p] : Set (GL (Fin 2) ℚ_[p])) * {padicDiagP p}) :
      Set (GL (Fin 2) ℚ_[p] ⧸ integralSubgroup ℤ_[p] ℚ_[p])).Finite :=
  finite_image_mul_diagPi (p : ℤ_[p]) (algebraMap_natCast_p_ne_zero p) PadicInt.irreducible_p

noncomputable def padicHeckeRep : Option (ZMod p) → GL (Fin 2) ℚ_[p]
  | some c => localRepSome (p : ℤ_[p]) (algebraMap_natCast_p_ne_zero p) ((ZMod.val c : ℕ) : ℤ_[p])
  | none => localRepInf (p : ℤ_[p]) (algebraMap_natCast_p_ne_zero p)

theorem isHeckeCosetSystem_padicHeckeRep :
    IsHeckeCosetSystem (integralSubgroup ℤ_[p] ℚ_[p]) (padicDiagP p) (padicHeckeRep p) := by
  constructor
  ·
    rintro (_ | c)
    · exact HeckePair.mem_doubleCoset_iff.mpr
        ⟨weylInt ℤ_[p] ℚ_[p], weylInt_mem, weylInt ℤ_[p] ℚ_[p], weylInt_mem, rfl⟩
    · exact HeckePair.mem_doubleCoset_iff.mpr
        ⟨unipotentInt ℚ_[p] ((ZMod.val c : ℕ) : ℤ_[p]), unipotentInt_mem _, 1, one_mem _,
          by rw [mul_one]; rfl⟩
  ·
    intro x hx
    obtain ⟨y, hy, u, hu, rfl⟩ := Set.mem_mul.mp hx
    have hu' : u ∈ integralSubgroup ℤ_[p] ℚ_[p] := hu
    have hy' : y ∈ heckeMulSet (p : ℤ_[p]) (algebraMap_natCast_p_ne_zero p) := hy
    have hmkx : (QuotientGroup.mk (y * u) :
          GL (Fin 2) ℚ_[p] ⧸ integralSubgroup ℤ_[p] ℚ_[p]) = QuotientGroup.mk y :=
      QuotientGroup.mk_mul_of_mem y hu'
    rcases exists_rep_of_mem_heckeMulSet (p : ℤ_[p]) (algebraMap_natCast_p_ne_zero p)
        PadicInt.irreducible_p hy' with ⟨b, hb⟩ | hbinf
    · obtain ⟨c, hc⟩ := exists_zmod_natCast_val_sub_dvd p b
      refine ⟨some c, ?_⟩
      have hbc := mk_localRepSome_eq_of_dvd_sub (p : ℤ_[p])
        (algebraMap_natCast_p_ne_zero p) hc
      show (QuotientGroup.mk (y * u) :
          GL (Fin 2) ℚ_[p] ⧸ integralSubgroup ℤ_[p] ℚ_[p]) = QuotientGroup.mk (padicHeckeRep p (some c))
      rw [hmkx, ← hb, hbc]
      rfl
    · refine ⟨none, ?_⟩
      show (QuotientGroup.mk (y * u) :
          GL (Fin 2) ℚ_[p] ⧸ integralSubgroup ℤ_[p] ℚ_[p]) = QuotientGroup.mk (padicHeckeRep p none)
      rw [hmkx, ← hbinf]
      rfl
  ·
    intro i j hij
    simp only at hij
    cases i with
    | none => cases j with
      | none => rfl
      | some c' =>
          exact absurd hij.symm (mk_localRepSome_ne_mk_localRepInf (p : ℤ_[p])
            (algebraMap_natCast_p_ne_zero p) PadicInt.irreducible_p.not_isUnit _)
    | some c => cases j with
      | none =>
          exact absurd hij (mk_localRepSome_ne_mk_localRepInf (p : ℤ_[p])
            (algebraMap_natCast_p_ne_zero p) PadicInt.irreducible_p.not_isUnit _)
      | some c' =>
          have hd := dvd_sub_of_mk_localRepSome_eq (p : ℤ_[p])
            (algebraMap_natCast_p_ne_zero p) hij
          exact congrArg some (zmod_eq_of_dvd_natCast_val_sub p hd)

end Padic

end HeckeIntegralSeam
