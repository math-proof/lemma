import Def.WeierstrassCurve_ModularityProps

set_option autoImplicit false

set_option maxHeartbeats 400000

noncomputable section

def Mlc1IsModularModelOfExactConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ Squarefree N ∧
    (∀ q : ℕ, q.Prime → (q ∣ N ↔ (q : ℤ) ∣ W.Δ)) ∧
    W.IsModularModelOfLevel N

def Mlc1ModularityLiftingAtConductor (p : ℕ) : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible p →
    W.IsResiduallyModular p → Mlc1IsModularModelOfExactConductorLevel W

def Mlc1RowStatement : Prop :=
  ∀ (p : ℕ), p = 3 ∨ p = 5 → Mlc1ModularityLiftingAtConductor p

end
