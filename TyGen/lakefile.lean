import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package stlc {
  moreLeanArgs := #["-D autoImplicit=false"]
  moreServerArgs := #["-D autoImplicit=false"]
}

lean_lib Stlc {
}

lean_lib Vect {
} 

 