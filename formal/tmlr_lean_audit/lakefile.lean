import Lake
open Lake DSL

package «tmlr-formal-audit» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

@[default_target]
lean_lib TmlrAudit where
