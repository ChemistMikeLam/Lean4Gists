import Lake

open System Lake DSL

package Lean4Gists where
  version := v!"0.1.0"
  description := "Collection of codes from my adventures in Lean 4"
  keywords := #[]
  homepage := "https://github.com/ChemistMikeLam/Lean4Gists"
  license := "GPL-3.0-or-later"
  licenseFiles := #["LICENSE"]
  readmeFile := "README.md"
  reservoir := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib Lean4Gists
