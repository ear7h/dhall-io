let IO = ./io.dhall
let IOMonad = IO.IOMonad
let s = IOMonad.return {} {=} : IO.IO {}
let s = IOMonad.bind {} {} s (λ(_ : {}) → IO.builtins.write 1 "1")
let s = IOMonad.bind {} {} s (λ(_ : {}) → IO.builtins.write 1 "2")
let s = IOMonad.bind {} {} s (λ(_ : {}) → IO.builtins.write 1 "3")
let s = IOMonad.bind {} {} s (λ(_ : {}) → IO.builtins.write 1 "4")
let s = IOMonad.bind {} {} s (λ(_ : {}) → IO.builtins.write 1 "5\n")
in s
