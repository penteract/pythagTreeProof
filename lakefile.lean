import Lake
open Lake DSL

package "proof" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  , ⟨`linter.unusedSimpArgs, false⟩
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «Proof» where
  -- add any library configuration options here
