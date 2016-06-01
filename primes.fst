module Primes

let op_Star = op_Multiply

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

val isPrime: x:pos -> Tot bool
let isPrime n = n <> 1 && isNotDivisor n 2 (n / 2)

type prime = x:pos{isPrime x}

let conclusion_0 (p:prime) (n:_{1 < n /\ n < p}): Tot (u:_{p <= 2 \/ isNotDivisor p n 1}) =
  let rec f n d r (a:int{isNotDivisor n d r /\ d <= a /\ a < d + r}):
      Tot (u:_{a * a > n \/ n % a <> 0}) (decreases r) =
    if d <> a then f n (d + 1) (r - 1) a
    in if n < p/2 then f p 2 (p/2) n

val gcd: a:nat -> b:nat -> Tot nat (decreases %[b;a])
let rec gcd a b =
  match b with
  | 0 -> a
  | _ -> gcd b (a % b)

val coprime: a:nat -> b:nat -> Tot bool
let coprime a b = gcd a b = 1

val fact_0: a:nat -> b:nat -> Lemma(coprime a b <==> gcd a b = 1)
let fact_0 a b = ()

//val abs: x:int -> Tot (y:int{ ((x >= 0) ==> (y = x)) /\ ((x < 0) ==> y = -x) })
//let abs x =
//  if x >= 0 then x
//  else -x

//val fact_5: a:pos -> b:pos -> Lemma(coprime a b <==> isPrime (abs (a - b)))
//let fact_5 a b = ()
