module

public import Mathlib
public import Def.NumberTheory.UnitaryDivisor.Part2

public section

open Nat
open Set


namespace Nat

/--
[mem_unitaryDivisors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
public theorem mem_unitaryDivisors
  {n d : ℕ} :
-- imply
  d ∈ unitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ d.Coprime (n / d) := by
-- proof
  simp [unitaryDivisors, Nat.mem_divisors, and_assoc]

end Nat

namespace Nat

/--
[unitaryDivisors_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
public theorem unitaryDivisors_zero
  :
-- imply
  unitaryDivisors 0 = ∅ := by
-- proof
  simp [unitaryDivisors]

end Nat

namespace Nat

/--
[coprime_div_of_mem_unitaryDivisors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
public theorem coprime_div_of_mem_unitaryDivisors
  {n d : ℕ}
-- given
  (h : d ∈ unitaryDivisors n) :
-- imply
  d.Coprime (n / d) :=
-- proof
  (mem_unitaryDivisors.mp h).2.2

end Nat

namespace Nat

/--
[sigmaStar_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
public theorem sigmaStar_eq_sum
  {n : ℕ} :
-- imply
  sigmaStar n = ∑ d ∈ unitaryDivisors n, d :=
-- proof
  rfl

end Nat

namespace Nat

/--
[sigmaStar_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
public theorem sigmaStar_zero
  :
-- imply
  sigmaStar 0 = 0 := by
-- proof
  simp [sigmaStar]
end Nat


namespace Set

/--
[isPrimitiveByDivisibility_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
public theorem isPrimitiveByDivisibility_iff
  {S : Set ℕ}
  {n : ℕ} :
-- imply
  S.IsPrimitiveByDivisibility n ↔
      n ∈ S ∧ ∀ {d : ℕ}, d ∣ n → d < n → d ∉ S := by
-- proof
  constructor
  · rintro ⟨hn, hdisjoint⟩
    refine ⟨hn, fun {d} hdvd hdlt hdS => ?_⟩
    exact Set.disjoint_left.mp hdisjoint (Nat.mem_properDivisors.mpr ⟨hdvd, hdlt⟩) hdS
  · rintro ⟨hn, hminimal⟩
    refine ⟨hn, Set.disjoint_left.mpr ?_⟩
    intro d hdproper hdS
    exact hminimal (Nat.mem_properDivisors.mp hdproper).1
      (Nat.mem_properDivisors.mp hdproper).2 hdS

end Set

namespace Set

/--
[IsPrimitiveByDivisibility.mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
public theorem IsPrimitiveByDivisibility.mem
  {S : Set ℕ}
  {n : ℕ}
-- given
  (h : S.IsPrimitiveByDivisibility n) :
-- imply
  n ∈ S :=
-- proof
  h.1

end Set

namespace Set

/--
[IsPrimitiveByDivisibility.not_mem_of_dvd_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
public theorem IsPrimitiveByDivisibility.not_mem_of_dvd_lt
  {S : Set ℕ}
  {n d : ℕ}
-- given
  (h : S.IsPrimitiveByDivisibility n)
  (hdvd : d ∣ n)
  (hdn : d < n) :
-- imply
  d ∉ S := by
-- proof
  intro hd
  exact isPrimitiveByDivisibility_iff.mp h |>.2 hdvd hdn hd

end Set

/--
[dvd_of_mem_unitaryDivisors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
public theorem dvd_of_mem_unitaryDivisors_eq
  {n d : ℕ}
-- given
  (h : d ∈ unitaryDivisors n) :
-- imply
  d ∣ n := by
-- proof
  apply Nat.dvd_of_mem_unitaryDivisors h


-- created on 2026-10-20
-- updated on 2026-10-26
