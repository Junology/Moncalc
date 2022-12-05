import Lake
open Lake DSL

package moncalc {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- @[defaultTarget]
lean_lib Moncalc {
  -- add any library configuration options here
}
