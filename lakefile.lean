import Lake
open Lake DSL

package «proof-ladders-cc» where
  buildDir := (get_config? verificationBuildDir).getD ".lake/build"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

/-- The library, from GitHub; `lake-manifest.json` pins the exact commit. -/
require ConstructiveCryptography from git
  "https://github.com/trailofbits/constructive-cryptography" @ "main"

@[default_target]
lean_lib ProofLadders where
  globs := #[.one `ProofLadders]
