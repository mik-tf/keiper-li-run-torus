import Lake
open Lake DSL

package p3lean where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Same pins as the paper 2 Lean directory (Mathlib v4.36.0, LeanCert v4.36.0), see lake-manifest.json.
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.36.0"
require leancert from git "https://github.com/alerad/leancert" @ "v4.36.0"

-- The pilot is plain Lean (no Mathlib import), so its kernel cost is measured alone.
@[default_target] lean_lib P3Lean
