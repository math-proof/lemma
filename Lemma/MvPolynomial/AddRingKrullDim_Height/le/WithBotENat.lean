import Mathlib
import sympy.Basic
open MvPolynomial


/--
[reverse_catenary_polynomial_ring](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  [Field k]
  {n : ℕ}
  {p : Ideal (MvPolynomial (Fin n) k)} [p.IsPrime] :
-- imply
  ringKrullDim (MvPolynomial (Fin n) k ⧸ p) + p.height ≤ (n : WithBot ENat) := by
-- proof
  set Rp := MvPolynomial (Fin n) k
  let pp : PrimeSpectrum Rp := ⟨p, inferInstance⟩
  have h_zeroLocus : PrimeSpectrum.zeroLocus (p : Set Rp) = Set.Ici pp := by
    ext q
    change p ≤ q.asIdeal ↔ pp ≤ q
    exact Iff.rfl
  have h_quot : ringKrullDim (Rp ⧸ p) = ↑(Order.coheight pp) := by
    rw [ringKrullDim_quotient, h_zeroLocus, ← Order.coheight_eq_krullDim_Ici]
  have h_ht : p.height = Order.height pp := by
    change pp.asIdeal.height = Order.height pp
    exact PrimeSpectrum.height_eq_orderHeight pp
  have : Nonempty (PrimeSpectrum Rp) := ⟨pp⟩
  have hbdd : BddAbove (Set.range fun a : PrimeSpectrum Rp =>
      Order.height a + Order.coheight a) :=
    OrderTop.bddAbove _
  have hsum : ↑(Order.height pp + Order.coheight pp) ≤
      Order.krullDim (PrimeSpectrum Rp) := by
    rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]
    exact le_ciSup hbdd pp
  have hdim : ringKrullDim Rp = (n : WithBot ENat) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      zero_add]
    simp [ENat.card_eq_coe_fintype_card]
  rw [h_quot, h_ht, ← WithBot.coe_add, add_comm]
  exact hsum.trans hdim.le


-- created on 2026-10-24
