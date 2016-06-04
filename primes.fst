module Primes

let op_Star = op_Multiply // reverse effect of --universes

type cexists (#a:Type) (p:a -> Type) : Type =
  | ExIntro : x:a -> h:p x -> cexists p

type divides (a:pos) (b:pos) = (cexists (fun (c:pos) -> (a*c) == b))

val notDivides: n:nat -> d:pos -> Tot bool
let notDivides n d = n % d <> 0

val isNotDivisor: n:nat -> d:pos -> r:nat -> Tot bool (decreases r)
let rec isNotDivisor n d runs =
  match runs with
  | 0 -> true
  | _ -> d * d > n || (notDivides n d && isNotDivisor n (d + 1) (runs - 1))

let isDivisor n d = not (notDivides n d)

val isPrime: x:pos -> Tot bool
let isPrime n = n <> 1 && isNotDivisor n 2 (n / 2)

type prime = x:pos{isPrime x}

type stream 'a =
  | Nil : stream 'a
  | Cons : hd:'a -> rest:(unit -> stream 'a) -> stream 'a

let rec from (n:pos) : stream pos =
  Cons n (fun () -> from (n + 1))

let rec filter (f: 'a -> bool) (s: stream 'a): stream 'a =
  match s with
  | Nil -> Nil
  | Cons x g ->
      if f x then Cons x (fun () -> filter f (g ()))
      else filter f (g ())

let sift (p:pos): stream pos -> stream pos =
  filter (fun (n:pos) -> notDivides n p)

let rec sieve (s: stream pos): stream pos =
  match s with
  | Nil -> Nil
  | Cons hd rst -> Cons hd (fun () -> sieve (sift hd (rst ())))

let primes = sieve (from 2)

let conclusion_0 (p:prime) (n:_{1 < n /\ n < p}): Lemma (p <= 2 \/ isNotDivisor p n 1) =
  let rec f n d r (a:int{isNotDivisor n d r /\ d <= a /\ a < d + r}):
      GTot (u:_{a * a > n \/ n % a <> 0}) (decreases r) =
    if d <> a then f n (d + 1) (r - 1) a
    in if n < p / 2 then f p 2 (p / 2) n

val gcd: a:nat -> b:nat -> Tot nat (decreases %[b;a])
let rec gcd a b =
  match b with
  | 0 -> a
  | _ -> gcd b (a % b)

val coprime: a:nat -> b:nat -> Tot bool
let coprime a b = gcd a b = 1

val fact_0: a:nat -> b:nat -> Lemma(coprime a b <==> gcd a b = 1)
let fact_0 a b = ()

val abs: x:int -> Tot nat
val abs: x:int -> Tot (y:int{((x >= 0) ==> (y = x)) /\ ((x < 0) ==> y = -x)})
let abs x =
  if x >= 0 then x
  else -x

val isZeroOrPrime: a:pos -> b:pos -> Tot bool
let isZeroOrPrime a b =
  match a - b with
  | 0 -> true
  | d -> isPrime (abs d)

type coprimes (a:pos) (b:pos) = (cexists (fun (c:pos) -> coprime a b))

let conclusion_1 (n:int{n > 2}) (m:int{m > 1 /\ m < n}): Lemma (true) = admit()
