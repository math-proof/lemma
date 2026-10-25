-- Carved from Lemma/Definitions/Def_LocalLanglands_PadicHeckeCosetSystem.lean: instance decls only.
import Mathlib
import Lemma.LocalLanglands.HeckeCosetLocal
import Structure.LocalLanglands_HeckeCosetSystem
import Lemma.LocalLanglands.PadicHeckeCosetSystem

set_option autoImplicit false

open scoped Pointwise ENNReal
open MulAction MeasureTheory

namespace HeckeIntegralSeam

section Padic

open LocalGL2

variable (p : ℕ) [hp : Fact p.Prime]

instance finite_padicInt_quotient_span_p : Finite (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine Finite.of_surjective
    (fun c : ZMod p => Ideal.Quotient.mk _ ((ZMod.val c : ℕ) : ℤ_[p])) fun b => ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨c, hc⟩ := exists_zmod_natCast_val_sub_dvd p b
  exact ⟨c, by rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]; exact hc⟩

end Padic

end HeckeIntegralSeam
