module

public import Mathlib.Data.PNat.Notation

public section

/-! # `ℕ⁺` for `PNat`

`ℕ⁺` is the positive natural numbers (`PNat`). The regular-plus form `ℕ+` is banned
in this repo — it reads as addition (`ℕ + n`); the superscript `⁺` is unambiguous.
-/

notation "ℕ⁺" => PNat
