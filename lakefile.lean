import Lake
open Lake DSL

package HigherCorrelations where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]
  -- OAI's patch hook requires dependencies beneath its own package root.
  packagesDir := ".lake/packages/OAI/lean/.lake/packages"

-- bootstrap_lean.py checks out and verifies the immutable upstream Git pin.
require OAI from ".lake/packages/OAI/lean"

@[default_target] lean_lib HigherCorrelations where
  srcDir := "lean"

lean_lib VerificationChallenges where
  srcDir := "lean"
