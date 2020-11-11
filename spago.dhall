{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "graphs"
, dependencies =
  [ "catenable-lists"
  , "console"
  , "effect"
  , "ordered-collections"
  , "psci-support"
  , "spec"
  , "unordered-collections"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
