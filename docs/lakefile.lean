import Lake

open System Lake DSL

package doc where
  version := v!"0.1.0"
  reservoir := false
  packagesDir := "../.lake/packages"

require Lean4Gists from "../"

require "leanprover" / «doc-gen4» @ git "v4.25.1"

