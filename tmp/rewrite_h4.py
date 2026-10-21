from pathlib import Path
p = Path("/home/cosmos/src/lean/Lemma/Random/ExpectFunPowDot/eq/Integral_Ext_FunPowDot/of/GtInftySup/All_Differentiable_Prob/All_NeProb_0/All_LeNormFunPowDot/All_MeasurableFun/IsPolicyTrajectory/In_Ico0.lean")
text = p.read_text()

text = text.replace(
    "  {X : (ℕ → ℝ) → (ℕ → S) → (ℕ → A) → ℕ → ℝ}\n  {B : ℝ}\n  {r :",
    "  {X : (ℕ → ℝ) → (ℕ → S) → (ℕ → A) → ℕ → ℝ}\n  {r :",
)

old_h4 = """  (h₄ : ∀ᵐ ω ∂(M θ), ∀ t,
    ‖((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => X (r · ω) (s · ω) (a · ω) (t + k)))‖ ≤ B)"""
new_h4 = """  (h₄ : ∀ᵐ ω ∂(M θ),
    sup[t] ‖((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => X (r · ω) (s · ω) (a · ω) (t + k)))‖ < ∞)"""
if old_h4 not in text:
    raise SystemExit("old h4 not found")
text = text.replace(old_h4, new_h4)

start_marker = "  let _ : MeasurableSpace Θ := borel Θ\n  have _ : BorelSpace Θ := ⟨rfl⟩\n  have hS :"
end_marker = "  let G : (ℕ → ℝ × S × A) → Θ := fun ω =>"
idx_start = text.find(start_marker)
idx_end = text.find(end_marker)
if idx_start < 0 or idx_end < 0:
    raise SystemExit(f"markers not found start={idx_start} end={idx_end}")

replacement = """  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  -- h₀/h₂/h₄/h₅/h₆ unused after Expect=∫ slim (kept on statement for of-atoms / callers)
  have _ := h₀
  have _ := h₂
  have _ := h₄
  have _ := h₅
  have _ := h₆
"""
text = text[:idx_start] + replacement + text[idx_end:]

ms_start = text.find("  obtain ⟨Ms, hMs⟩ : ∃ Ms : ℝ, Ms = ∑ q : S × A,")
gsm_start = text.find("  have hGsm : StronglyMeasurable G := by")
if ms_start < 0 or gsm_start < 0:
    raise SystemExit(f"Ms/hGsm markers not found ms={ms_start} gsm={gsm_start}")
text = text[:ms_start] + text[gsm_start:]

assert "{B : ℝ}" not in text
assert "sup[t]" in text
assert "obtain ⟨Ms, hMs⟩" not in text
assert "have hFb" not in text
assert "have hGsm" in text
assert "exact hpath" in text
p.write_text(text)
print("ok", len(text))
