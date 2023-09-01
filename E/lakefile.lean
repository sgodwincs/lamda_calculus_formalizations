import Lake
open Lake DSL

require aesop from git "https://github.com/JLimperg/aesop"

package stlc {
  moreLeanArgs := #["-D autoImplicit=false"]
  moreServerArgs := #["-D autoImplicit=false"]
}

lean_lib Stlc {
}

lean_lib Vector {
}

 