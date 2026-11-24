module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.GroupTheory.BurnsidePaqb.SimplePrime
public import Theorem.Complex.False.of.EqAdd1Mul_0.IsIntegral.Prime
public import Theorem.Nat.Any_Eq_MulPowS.of.Prime.Prime


public section

namespace BurnsidePaqb

/--
[burnside_paqb_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb.lean)
-/
private theorem burnside_paqb_zero
  [Group G] [Fintype G]
  {p q a b : ℕ}
-- given
  (hp : Nat.Prime p)
  (hq : Nat.Prime q)
  (hcard : Fintype.card G = p ^ a * q ^ b) :
-- imply
  Group.IsSolvable G :=
-- proof
  burnside_paqb_of_simple_prime
    (fun hH hg => by
      have := hH
      obtain ⟨g, hg1, hpp⟩ := hg
      exact cor6_of_prime_pow_class (g := g) hg1 hpp)
    (p := p) (q := q) (a := a) (b := b) hp hq hcard

/--
[burnside_paqb](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb.lean)
-/
theorem burnside_paqb
  [Group G] [Fintype G]
-- given
  (p q a b : ℕ)
  (hp : Nat.Prime p)
  (hq : Nat.Prime q)
  (hcard : Fintype.card G = p ^ a * q ^ b) :
-- imply
  Group.IsSolvable G := by
-- proof
  classical
  set n := Fintype.card G with hn
  set e : G ≃ Fin n := Fintype.equivFin G with he
  let mulFin : Mul (Fin n) := ⟨fun x y => e (e.symm x * e.symm y)⟩
  let oneFin : One (Fin n) := ⟨e 1⟩
  let invFin : Inv (Fin n) := ⟨fun x => e (e.symm x)⁻¹⟩
  let divFin : Div (Fin n) := ⟨fun x y => e (e.symm x / e.symm y)⟩
  let npowFin : Pow (Fin n) ℕ := ⟨fun x k => e (e.symm x ^ k)⟩
  let zpowFin : Pow (Fin n) ℤ := ⟨fun x k => e (e.symm x ^ k)⟩
  have hone : e.symm oneFin.one = 1 := by
    rw [show oneFin.one = e 1 from rfl]
    exact e.symm_apply_apply 1
  have hmul : ∀ x y : Fin n, e.symm (x * y) = e.symm x * e.symm y :=
    fun x y => e.symm_apply_apply _
  have hinv : ∀ x : Fin n, e.symm x⁻¹ = (e.symm x)⁻¹ :=
    fun x => e.symm_apply_apply _
  have hdiv : ∀ x y : Fin n, e.symm (x / y) = e.symm x / e.symm y :=
    fun x y => e.symm_apply_apply _
  have hnpow : ∀ (x : Fin n) (k : ℕ), e.symm (x ^ k) = e.symm x ^ k := by
    intro x k
    rw [show (x ^ k) = e (e.symm x ^ k) from rfl]
    exact e.symm_apply_apply _
  have hzpow : ∀ (x : Fin n) (k : ℤ), e.symm (x ^ k) = e.symm x ^ k := by
    intro x k
    rw [show (x ^ k) = e (e.symm x ^ k) from rfl]
    exact e.symm_apply_apply _
  let : Group (Fin n) := Function.Injective.group (e.symm : Fin n → G)
    e.symm.injective hone hmul hinv hdiv hnpow hzpow
  have hcardH : Fintype.card (Fin n) = p ^ a * q ^ b := by
    rwa [Fintype.card_fin]
  have hsolH : Group.IsSolvable (Fin n) :=
    burnside_paqb_zero (p := p) (q := q) (a := a) (b := b) hp hq hcardH
  let E : (Fin n) →* G :=
    { toFun := e.symm, map_one' := hone, map_mul' := hmul }
  have hEsurj : Function.Surjective E := fun b => ⟨e b, e.symm_apply_apply b⟩
  have hrange : E.range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, hx⟩ := hEsurj y
    exact ⟨x, hx⟩
  let T : G →* Unit :=
    { toFun := fun _ => (), map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hle : T.ker ≤ E.range := by
    rw [hrange]
    exact le_top
  have := hsolH
  exact Group.isSolvable_of_ker_le_range E T hle

end BurnsidePaqb


-- created on 2026-10-20
-- updated on 2026-11-23
