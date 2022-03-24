let Prelude = https://raw.githubusercontent.com/dhall-lang/dhall-lang/v21.1.0/Prelude/package.dhall
let List/map = Prelude.List.map
let List/concat = Prelude.List.concat
let List/foldLeft = Prelude.List.foldLeft
let Optional/map = Prelude.Optional.map

let Functor =
	λ(F : Type → Type) →
	{ map :
		∀(a : Type) → ∀(b : Type) →
		(a → b) → F a  → F b
	}

let Bifunctor =
	λ(F : Type → Type → Type) →
	{ bimap :
		∀(a : Type) → ∀(b : Type) →
		∀(c : Type) → ∀(d : Type) →
		(a → b) → (c → d) → F a c → F b d
	}

let Applicative =
	λ(F : Type → Type) →
		(Functor F) //\\
		{ pure : ∀(a : Type) → a → F a
		, apply :
			∀(a : Type) → ∀(b : Type) →
			F (a → b) → F a → F b
		}

let Monad =
	λ(M : Type → Type) →
		(Applicative M) //\\
		{ return : ∀(a : Type) → a → M a
		, bind :
			∀(a : Type) → ∀(b : Type) →
			M a → (a → M b) → M b
		}

let foldLeftM :
	∀(m : Type → Type) → Monad m → ∀(a : Type) → ∀(b : Type) →
	(b → a → m b) → b → List a → m b
	=
	λ(m : Type → Type) → λ(mfs : Monad m) → λ(a : Type) → λ(b : Type) →
	λ(f : b → a → m b) → λ(init : b) → λ(xs : List a) →
	let cons : m b → a → m b =
		λ(acc : m b) → λ(el : a) → mfs.bind b b acc (λ(x : b) → f x el)
	in List/foldLeft a xs (m b) cons (mfs.return b init)

let foldM :
	∀(m : Type → Type) → Monad m → ∀(a : Type) → ∀(b : Type) →
	(a → b → m b) → b → List a → m b
	=
	λ(m : Type → Type) → λ(mfs : Monad m) → λ(a : Type) → λ(b : Type) →
	λ(f : a → b  → m b) → λ(init : b) → λ(xs : List a) →
	let cons : a → m b → m b =
		λ(el : a) → λ(acc : m b) → mfs.bind b b acc (f el)
	in List/fold a xs (m b) cons (mfs.return b init)

let mapM :
	∀(m : Type → Type) → Monad m → ∀(a : Type) → ∀(b : Type) →
	(a → m b) → List a → m (List b)
	=
	λ(m : Type → Type) → λ(mfs : Monad m) → λ(a : Type) → λ(b : Type) →
	λ(f : a → m b) → λ(xs : List a) →
	let go = λ(acc : List b) → λ(el : a) →
		mfs.map b (List b) (λ(el1 : b) → acc # [el1]) (f el)
	in foldLeftM m mfs a (List b) go ([] : List b) xs


let ListFunctor : Functor List =
	{ map = List/map
	}

let ListApplicative : Applicative List =
	ListFunctor /\
	{ pure = λ(a : Type) → λ(x : a) → [x]
	, apply =
		λ(a : Type) → λ(b : Type) →
		λ(f : List (a → b)) → λ(xs : List a) →
		let go : (a → b) → List b = λ(f1 : (a → b)) → List/map a b f1 xs
		in List/concat b (List/map (a → b) (List b) go f)
	}

let ListMonad : Monad List =
	ListApplicative /\
	{ return = ListApplicative.pure
	, bind =
		λ(a : Type) → λ(b : Type) →
		λ(xs : List a) → λ(f : a → List b) →
		List/concat b (List/map a (List b) f xs)
	}

let OptionalFunctor : Functor Optional =
	{ map = Optional/map
	}

let OptionalApplicative : Applicative Optional =
	OptionalFunctor /\
	{ pure = λ(a : Type) → λ(x : a) → Some x
	, apply =
		λ(a : Type) → λ(b : Type) →
		λ(f : Optional (a → b)) → λ(x : Optional a) →
		merge
			{ None = None b
			, Some = λ(f : a → b) → OptionalFunctor.map a b f x
			}
			f
	}

let OptionalMonad : Monad Optional =
	OptionalApplicative /\
	{ return = OptionalApplicative.pure
	, bind =
		λ(a : Type) → λ(b : Type) →
		λ(x : Optional a) → λ(f : a → Optional b) →
		merge
			{ None = None b
			, Some = f
			}
			x
	}

let Result = λ(E : Type) → λ(T : Type) → < Ok : T | Err : E >

let ResultFunctor : ∀(e : Type) → Functor (Result e) =
	λ(e : Type) →
	{ map =
		λ(a : Type) → λ(b : Type) →
		λ(f : a → b) → λ(r : Result e a) →
		merge
			{ Ok = λ(x : a) → (Result e b).Ok (f x)
			, Err = λ(x : e) → (Result e b).Err x
			}
			r
	}

let ResultBifunctor : Bifunctor Result =
	{ bimap =
		λ(a : Type) → λ(b : Type) → λ(c : Type) → λ(d : Type) →
		λ(f1 : a → b) → λ(f2 : c → d) → λ(r : Result a c) →
		merge
			{ Err = λ(x : a) → (Result b d).Err (f1 x)
			, Ok = λ(x : c) → (Result b d).Ok (f2 x)
			}
			r
	}

let ResultApplicative : ∀(e : Type) → Applicative (Result e) =
	λ(e : Type) →
	(ResultFunctor e) /\
	{ pure = λ(a : Type) → (Result e a).Ok
	, apply =
		λ(a : Type) → λ(b : Type) →
		λ(f : Result e (a → b)) → λ(x : Result e a) →
		merge
			{ Err = (Result e b).Err
			, Ok = λ(f : a → b) → (ResultFunctor e).map a b f x
			}
			f
	}

let ResultMonad : ∀(e : Type) → Monad (Result e) =
	λ(e : Type) →
	(ResultApplicative e) /\
	{ return = (ResultApplicative e).pure
	, bind =
		λ(a : Type) → λ(b : Type) →
		λ(ma : Result e a) → λ(f : a → Result e b) →
		merge
			{ Err = (Result e b).Err
			, Ok = f
			}
			ma
	}

let exampleFilter = λ(n : Natural) →
	let m = ResultMonad Text
	let Result = Result Text
	let evens = λ(x : Natural) →
		if Prelude.Natural.even x
		then (Result Natural).Ok x
		else (Result Natural).Err "not even!"
	let digits = λ(x : Natural) →
		if Prelude.Natural.lessThan x 10
		then (Result Natural).Ok x
		else (Result Natural).Err "not a digit!"
	let myShow = λ(x : Natural) →
		if Prelude.Natural.equal x 2
		then (Result Text).Ok "2"
		else (Result Text).Err "show not implemented!"
	in
		-- the closest we can get to do notation
		let res = m.return Natural n
		let res = m.bind Natural Natural res evens
		let res = m.bind Natural Natural res digits
		in m.bind Natural Text res myShow

let example0 =
	assert : exampleFilter 1 ≡ (Result Text Text).Err "not even!"
let example1 =
	assert : exampleFilter 20 ≡ (Result Text Text).Err "not a digit!"
let example2 =
	assert : exampleFilter 4 ≡ (Result Text Text).Err "show not implemented!"
let example3  =
	assert : exampleFilter 2 ≡ (Result Text Text).Ok "2"

in
{ Functor
, Bifunctor
, Applicative
, Monad

, foldLeftM
, foldM
, mapM

, ListFunctor
, ListApplicative
, ListMonad

, OptionalFunctor
, OptionalApplicative
, OptionalMonad

, Result
, ResultFunctor
, ResultBifunctor
, ResultApplicative
, ResultMonad

, example0
, example1
, example2
, example3
}
