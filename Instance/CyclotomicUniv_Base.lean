-- Carved from Lemma/Definitions/Def_CyclotomicUniv_Base.lean: instance decls only.
import Mathlib
import Lemma.CyclotomicUniv.Base

set_option autoImplicit false

noncomputable section

open Polynomial

namespace CyclotomicUniv

variable (N : ℕ)

section Basic

variable [NeZero N]

instance instIsDomainR₀ : IsDomain (R₀ N) :=
  AdjoinRoot.isDomain_of_prime (cyclotomic.irreducible (NeZero.pos N)).prime

instance instCharZeroR₀ : CharZero (R₀ N) where
  cast_injective a b h := by
    have h' : AdjoinRoot.of (cyclotomic N ℤ) (a : ℤ) = AdjoinRoot.of (cyclotomic N ℤ) (b : ℤ) := by
      rwa [map_natCast, map_natCast]
    exact_mod_cast of_injective N h'

instance instIsDomain : IsDomain (base N) :=
  IsLocalization.isDomain_localization (powers_den_le N)

instance instCharZero : CharZero (base N) where
  cast_injective a b h := by
    have h' : algebraMap (R₀ N) (base N) (a : R₀ N) = algebraMap (R₀ N) (base N) (b : R₀ N) := by
      rwa [map_natCast, map_natCast]
    exact_mod_cast algebraMap_injective N h'

end Basic


end CyclotomicUniv

end
