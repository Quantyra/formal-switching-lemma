import Lake
open Lake DSL

package formal_switching_lemma where
  -- Publication artifact for the Lean-checked SimpleDNF switching lemma and
  -- bounded-depth explicit layer-collapse infrastructure.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.13.0"

@[default_target]
lean_lib PvNP where
  srcDir := "lean"
