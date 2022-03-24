let Prelude = https://raw.githubusercontent.com/dhall-lang/dhall-lang/v21.1.0/Prelude/package.dhall

let Natural/max = Prelude.Natural.max
let Natural/equal = Prelude.Natural.equal
let Optional/null = Prelude.Optional.null

let M = ./package.dhall
let Functor = M.Functor
let Applicative = M.Applicative
let Monad = M.Monad

let IOError = < EOF | PermissionDenied | BadFD | Other : Text >
let Result = M.Result IOError
let ResultMonad = M.ResultMonad IOError

let FileMode =
	{ read : Bool
	, write : Bool
	, create : Bool
	, truncate : Bool
	, append : Bool
	}

let File =
	{ fd : Natural
	, name : Text
	, inData : Text
	, outData : Text
	, mode : FileMode
	}

-- let World : Type = mkBuiltins Result
let World =
	{ time : Natural
	, files : List File
	}

let Syscall =
	-- open the file
	< Open : { _1 : Text, _2 : FileMode }
	-- read from an fd
	| Read : Natural
	-- write to an fd
	| Write : { _1 : Natural, _2 : Text }
	-- close the file
	| Close : Natural
	-- exit code
	| Exit : Natural
	-- update the time value
	| Time
	>

let WorldResult : Type → Type =
	λ(a : Type) →
	{ value : Result a
	, world : World
	}

let IO/step : World → Syscall → WorldResult {} =
	λ(w : World) → λ(s : Syscall) →
	let res = IO/step w s
	let value = merge
		{ None = (Result {}).Ok {=}
		, Some = (Result {}).Err
		}
		res.err
	in { world = res.world, value }

let mapW = λ(a : Type) → λ(b : Type) →
	λ(f : (a → b)) → λ(w : WorldResult a) →
	w // { value = ResultMonad.map a b f w.value }

let setW = λ(a : Type) →
	λ(x : a) → λ(w : WorldResult {}) →
	let const = λ(_ : {}) → x
	in w // { value = ResultMonad.map {} a const w.value }

let setRW = λ(a : Type) →
	λ(x : Result a) → λ(w : WorldResult {}) →
	let const = λ(_ : {}) → x
	in w // { value = ResultMonad.bind {} a w.value const }


let IO : Type → Type =
	λ(a : Type) →
	World → WorldResult a


let IOFunctor : Functor IO =
	{ map =
		λ(a : Type) → λ(b : Type) →
		λ(f : a → b) → λ(x : IO a) →
		λ(i : World) → mapW a b f (x i)
	}

let IOApplicative : Applicative IO =
	IOFunctor /\
	{ pure =
		λ(a : Type) → λ(x : a) →
		λ(w : World) → { world = w, value = ResultMonad.pure a x }
	, apply =
		λ(a : Type) → λ(b : Type) →
		λ(f : IO (a → b)) → λ(x : IO a) →
		λ(w : World) →
		let rf = f w
		in merge
			{ Ok = λ(f : (a → b)) → mapW a b f (x rf.world)
			, Err = λ(e : IOError) → rf // { value = (Result b).Err e }
			}
			rf.value
	}

let IOMonad : Monad IO =
	IOApplicative /\
	{ return = λ(a : Type) → λ(x : a) → IOApplicative.pure a x
	, bind =
		λ(a : Type) → λ(b : Type) →
		λ(x : IO a) → λ(f : a → IO b) →
		λ(w : World) →
		let rx = x w
		in merge
			{ Ok = λ(x : a) → (f x) rx.world
			, Err = λ(e : IOError) → rx // { value = (Result b).Err e }
			}
			rx.value
	}

let Builtins =
	{ open : Text → FileMode → IO Natural
	, read : Natural → IO Text
	, write : Natural → Text → IO {}
	, close : Natural → IO {}
	, exit : Natural → IO {}
	, time : IO Natural
	}

let builtins : Builtins =
	{ open =
		λ(name : Text) → λ(mode : FileMode) →
		λ(w : World) →
		let wr = IO/step w (Syscall.Open { _1 = name, _2 = mode, })
		let nextFD = merge
			{ None = (Result Natural).Err (IOError.Other "IO/step failure")
			, Some = λ(f : File) → (Result Natural).Ok f.fd
			}
			(List/head File wr.world.files)
		in setRW Natural nextFD wr
	, write =
		λ(fd : Natural) → λ(buf : Text) →
		λ(w : World) →
		IO/step w (Syscall.Write { _1 = fd, _2 = buf })
	, read =
		λ(fd : Natural) →
		λ(w : World) →
		let wr = IO/step w (Syscall.Read fd)
		let buf = List/fold File wr.world.files (Result Text)
			(λ(file : File) → λ(r : Result Text) →
				if Natural/equal file.fd fd
				then (Result Text).Ok file.outData
				else r
			)
			((Result Text).Err IOError.BadFD)
		in setRW Text buf wr
	, close =
		λ(fd : Natural) →
		λ(w : World) →
		IO/step w (Syscall.Close fd)
	, exit =
		λ(code : Natural) →
		λ(w : World) →
		IO/step w (Syscall.Exit code)
	, time =
		λ(w : World) →
		let wr = IO/step w Syscall.Time
		in setW Natural wr.world.time wr
	}

in
{ IO
, IOFunctor
, IOApplicative
, IOMonad

, Builtins
, builtins

, stdin = 0
, stdout = 1
, stderr = 2
}
