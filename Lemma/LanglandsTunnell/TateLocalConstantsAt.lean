import Lemma.LanglandsTunnell.TateLocalZeta
import Lemma.NumberField.AdelicLevel
import Def.LanglandsTunnell_TateLocalConstantsAt

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.TateLocal

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))


theorem mem_higherUnitsAt_iff {n : ℕ} {u : (v.adicCompletion K)ˣ} :
    u ∈ higherUnitsAt K v n ↔ Valued.v (u : v.adicCompletion K) = 1 ∧
      (n = 0 ∨ Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ))) :=
  Iff.rfl

theorem mem_higherUnitsAt_zero_iff {u : (v.adicCompletion K)ˣ} :
    u ∈ higherUnitsAt K v 0 ↔ Valued.v (u : v.adicCompletion K) = 1 := by
  simp [mem_higherUnitsAt_iff]

theorem one_mem_higherUnitsAt (n : ℕ) : (1 : (v.adicCompletion K)ˣ) ∈ higherUnitsAt K v n := by
  refine ⟨by simp, ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Or.inl h
  · right
    simp only [Units.val_one, sub_self, map_zero]
    exact zero_le

theorem higherUnitsAt_antitone : Antitone (higherUnitsAt K v) := by
  intro m n hmn u hu
  obtain ⟨hval, hball⟩ := hu
  refine ⟨hval, ?_⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact Or.inl hm
  · right
    rcases hball with hn0 | hle
    · omega
    · exact hle.trans (WithZero.exp_le_exp.mpr (by omega))


theorem hasConductorExponentAt_zero_iff {χ : (v.adicCompletion K)ˣ →* ℂˣ} :
    HasConductorExponentAt K v χ 0 ↔
      ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ u = 1 := by
  constructor
  · intro h u hu
    exact h.1 u ((mem_higherUnitsAt_zero_iff K v).mpr hu)
  · intro h
    exact ⟨fun u hu => h u ((mem_higherUnitsAt_zero_iff K v).mp hu),
      fun m hm => absurd hm (Nat.not_lt_zero m)⟩

theorem hasConductorExponentAt_unique {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c c' : ℕ}
    (h : HasConductorExponentAt K v χ c) (h' : HasConductorExponentAt K v χ c') : c = c' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨u, hu, hne1⟩ := h'.2 c hlt
    exact hne1 (h.1 u hu)
  · obtain ⟨u, hu, hne1⟩ := h.2 c' hgt
    exact hne1 (h'.1 u hu)

theorem hasConductorExponentAt_one_zero :
    HasConductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) 0 :=
  (hasConductorExponentAt_zero_iff K v).mpr fun _ _ => rfl

theorem not_hasConductorExponentAt_one_succ (c : ℕ) :
    ¬ HasConductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) (c + 1) := by
  rintro ⟨-, hmin⟩
  obtain ⟨u, -, hne⟩ := hmin c (Nat.lt_succ_self c)
  exact hne rfl


theorem conductorExponentAt_eq_of_hasConductorExponentAt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ}
    (h : HasConductorExponentAt K v χ c) : conductorExponentAt K v χ = c := by
  have hmem : c ∈ {c' | HasConductorExponentAt K v χ c'} := h
  have hle : conductorExponentAt K v χ ≤ c := Nat.sInf_le hmem
  have hge : c ≤ conductorExponentAt K v χ := by
    have hne : {c' | HasConductorExponentAt K v χ c'}.Nonempty := ⟨c, h⟩
    have hmemInf := Nat.sInf_mem hne
    exact (hasConductorExponentAt_unique K v hmemInf h).ge
  omega

@[simp] theorem conductorExponentAt_one :
    conductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) = 0 :=
  conductorExponentAt_eq_of_hasConductorExponentAt K v (hasConductorExponentAt_one_zero K v)


theorem localLFactorAt_of_hasConductorExponentAt_zero {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : HasConductorExponentAt K v χ 0) (s : ℂ) :
    localLFactorAt K v χ s
      = (1 - (χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [localLFactorAt, if_pos hχ]

theorem localLFactorAt_of_not_hasConductorExponentAt_zero {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : ¬ HasConductorExponentAt K v χ 0) (s : ℂ) : localLFactorAt K v χ s = 1 := by
  rw [localLFactorAt, if_neg hχ]

theorem localLFactorAt_one (s : ℂ) :
    localLFactorAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) s
      = (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [localLFactorAt_of_hasConductorExponentAt_zero K v (hasConductorExponentAt_one_zero K v),
    MonoidHom.one_apply, Units.val_one, one_mul]

section Epsilon

variable [MeasurableSpace (v.adicCompletion K)]


theorem localEpsilonAt_def (μ : Measure (v.adicCompletion K)) (ψ : AddChar (v.adicCompletion K) ℂ)
    (f : v.adicCompletion K → ℂ) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) :
    localEpsilonAt K v μ ψ f χ s
      = localGammaAt μ ψ f χ s * localLFactorAt K v χ s / localLFactorAt K v χ⁻¹ (1 - s) :=
  rfl

theorem localEpsilonAt_of_not_hasConductorExponentAt_zero (μ : Measure (v.adicCompletion K))
    (ψ : AddChar (v.adicCompletion K) ℂ) (f : v.adicCompletion K → ℂ)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hχ : ¬ HasConductorExponentAt K v χ 0) (s : ℂ) :
    localEpsilonAt K v μ ψ f χ s = localGammaAt μ ψ f χ s := by
  have hχ' : ¬ HasConductorExponentAt K v χ⁻¹ 0 := fun h => hχ <| by
    rw [hasConductorExponentAt_zero_iff] at h ⊢
    intro u hu
    have := h u hu
    rwa [MonoidHom.inv_apply, inv_eq_one] at this
  rw [localEpsilonAt, localLFactorAt_of_not_hasConductorExponentAt_zero K v hχ,
    localLFactorAt_of_not_hasConductorExponentAt_zero K v hχ', mul_one, div_one]

theorem localEpsilonAt_eq_zero_of_localZeta_eq_zero {μ : Measure (v.adicCompletion K)}
    {ψ : AddChar (v.adicCompletion K) ℂ} {f : v.adicCompletion K → ℂ}
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {s : ℂ} (h : localZeta μ f χ s = 0) :
    localEpsilonAt K v μ ψ f χ s = 0 := by
  sorry

end Epsilon

end LanglandsTunnell.TateLocal

end
