import Lake
open Lake DSL

require aesop from git "https://github.com/JLimperg/aesop"

package e {
  moreLeanArgs := #["-D autoImplicit=false"]
  -- add package configuration options here
}

lean_lib E {
  -- add library configuration options here
}

lean_lib Vector {
  -- add library configuration options here
}

@[default_target]
lean_exe e {
  root := `Main
  buildType := .minSizeRel
}
