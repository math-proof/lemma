import Mathlib
import Def.FLTPrelim_Modularity
import Def.CuspForm_PrimitiveFormGamma1

set_option autoImplicit false

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups

namespace CuspForm

variable {M : ℕ} {k : ℤ}


theorem IsEigenformWith.qCoeff_one {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) : qCoeff g 1 = 1 := h.1

theorem IsEigenformWith.hecke_of_not_dvd {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (n : ℕ) :
    qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff g (n / p) else 0) =
      qCoeff g p * qCoeff g n := h.2.1 p hp hpM n

theorem IsEigenformWith.hecke_of_dvd {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) (n : ℕ) :
    qCoeff g (ℓ * n) = qCoeff g ℓ * qCoeff g n := h.2.2.1 ℓ hℓ hℓM n

theorem IsEigenformWith.hasNebentypus {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) : HasNebentypus ε g := h.2.2.2

theorem IsPrimitiveForm.isEigenformWith {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsPrimitiveForm ε g) : IsEigenformWith ε g := h.1

theorem IsPrimitiveForm.not_eigenpacketOccursAt {ε : DirichletCharacter ℂ M}
    {g : CuspForm (Gamma1 M) k} (h : IsPrimitiveForm ε g) {M' : ℕ} (hM' : M' ∣ M) (hne : M' ≠ M) :
    ¬ EigenpacketOccursAt k (fun n => qCoeff g n) (fun n => ε (n : ZMod M)) M' := h.2 M' hM' hne

theorem IsEigenformWith.eigenpacketOccursAt {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) (hM : M ≠ 0) (hg : g ≠ 0) :
    EigenpacketOccursAt k (fun n => qCoeff g n) (fun n => ε (n : ZMod M)) M :=
  ⟨ε, g, hg, h.hasNebentypus, Nat.divisors M, fun _ hp hpS => ⟨rfl, fun n =>
    h.hecke_of_not_dvd hp (fun hpM => hpS (Nat.mem_divisors.2 ⟨hpM, hM⟩)) n⟩⟩

end CuspForm
