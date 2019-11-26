object foveSIMM {

abstract sealed class int
final case class int_of_integer(a: BigInt) extends int

def integer_of_int(x0: int): BigInt = x0 match {
  case int_of_integer(k) => k
}

def equal_inta(k: int, l: int): Boolean = integer_of_int(k) == integer_of_int(l)

trait equal[A] {
  val `foveSIMM.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean =
  A.`foveSIMM.equal`(a, b)
object equal {
  implicit def `foveSIMM.equal_char`: equal[char] = new equal[char] {
    val `foveSIMM.equal` = (a: char, b: char) => equal_chara(a, b)
  }
  implicit def `foveSIMM.equal_list`[A : equal]: equal[List[A]] = new
    equal[List[A]] {
    val `foveSIMM.equal` = (a: List[A], b: List[A]) => equal_lista[A](a, b)
  }
  implicit def `foveSIMM.equal_int`: equal[int] = new equal[int] {
    val `foveSIMM.equal` = (a: int, b: int) => equal_inta(a, b)
  }
}

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

def equal_lista[A : equal](x0: List[A], x1: List[A]): Boolean = (x0, x1) match {
  case (Nil, x21 :: x22) => false
  case (x21 :: x22, Nil) => false
  case (x21 :: x22, y21 :: y22) => eq[A](x21, y21) && equal_lista[A](x22, y22)
  case (Nil, Nil) => true
}

def times_int(k: int, l: int): int =
  int_of_integer(integer_of_int(k) * integer_of_int(l))

abstract sealed class rat
final case class Frct(a: (int, int)) extends rat

def quotient_of(x0: rat): (int, int) = x0 match {
  case Frct(x) => x
}

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

def sgn_integer(k: BigInt): BigInt =
  (if (k == BigInt(0)) BigInt(0)
    else (if (k < BigInt(0)) BigInt(-1) else BigInt(1)))

def apsnd[A, B, C](f: A => B, x1: (C, A)): (C, B) = (f, x1) match {
  case (f, (x, y)) => (x, f(y))
}

def comp[A, B, C](f: A => B, g: C => A): C => B = ((x: C) => f(g(x)))

def divmod_integer(k: BigInt, l: BigInt): (BigInt, BigInt) =
  (if (k == BigInt(0)) (BigInt(0), BigInt(0))
    else (if (l == BigInt(0)) (BigInt(0), k)
           else (comp[BigInt, ((BigInt, BigInt)) => (BigInt, BigInt),
                       BigInt](comp[BigInt => BigInt,
                                     ((BigInt, BigInt)) => (BigInt, BigInt),
                                     BigInt](((a: BigInt => BigInt) =>
       (b: (BigInt, BigInt)) => apsnd[BigInt, BigInt, BigInt](a, b)),
      ((a: BigInt) => (b: BigInt) => a * b)),
                                ((a: BigInt) =>
                                  sgn_integer(a)))).apply(l).apply((if (sgn_integer(k) ==
                                  sgn_integer(l))
                             ((k: BigInt) => (l: BigInt) => if (l == 0)
                               (BigInt(0), k) else
                               (k.abs /% l.abs)).apply(k).apply(l)
                             else {
                                    val (r, s): (BigInt, BigInt) =
                                      ((k: BigInt) => (l: BigInt) => if (l == 0)
(BigInt(0), k) else (k.abs /% l.abs)).apply(k).apply(l);
                                    (if (s == BigInt(0)) ((- r), BigInt(0))
                                      else ((- r) - BigInt(1), l.abs - s))
                                  }))))

def fst[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def divide_integer(k: BigInt, l: BigInt): BigInt =
  fst[BigInt, BigInt](divmod_integer(k, l))

def divide_int(k: int, l: int): int =
  int_of_integer(divide_integer(integer_of_int(k), integer_of_int(l)))

def uminus_int(k: int): int = int_of_integer((- (integer_of_int(k))))

def zero_int: int = int_of_integer(BigInt(0))

def less_int(k: int, l: int): Boolean = integer_of_int(k) < integer_of_int(l)

def one_int: int = int_of_integer(BigInt(1))

def gcd_int(x0: int, x1: int): int = (x0, x1) match {
  case (int_of_integer(x), int_of_integer(y)) => int_of_integer(x.gcd(y))
}

def snd[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

def normalize(p: (int, int)): (int, int) =
  (if (less_int(zero_int, snd[int, int](p)))
    {
      val a: int = gcd_int(fst[int, int](p), snd[int, int](p));
      (divide_int(fst[int, int](p), a), divide_int(snd[int, int](p), a))
    }
    else (if (equal_inta(snd[int, int](p), zero_int)) (zero_int, one_int)
           else {
                  val a: int =
                    uminus_int(gcd_int(fst[int, int](p), snd[int, int](p)));
                  (divide_int(fst[int, int](p), a),
                    divide_int(snd[int, int](p), a))
                }))

def times_rat(p: rat, q: rat): rat =
  Frct({
         val a: (int, int) = quotient_of(p)
         val (aa, c): (int, int) = a
         val b: (int, int) = quotient_of(q)
         val (ba, d): (int, int) = b;
         normalize((times_int(aa, ba), times_int(c, d)))
       })

abstract sealed class real
final case class Ratreal(a: rat) extends real

def times_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(times_rat(x, y))
}

trait times[A] {
  val `foveSIMM.times`: (A, A) => A
}
def times[A](a: A, b: A)(implicit A: times[A]): A = A.`foveSIMM.times`(a, b)
object times {
  implicit def `foveSIMM.times_real`: times[real] = new times[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
  }
}

trait dvd[A] extends times[A] {
}
object dvd {
  implicit def `foveSIMM.dvd_real`: dvd[real] = new dvd[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
  }
}

def uminus_rat(p: rat): rat = Frct({
                                     val a: (int, int) = quotient_of(p)
                                     val (aa, b): (int, int) = a;
                                     (uminus_int(aa), b)
                                   })

def uminus_reala(x0: real): real = x0 match {
  case Ratreal(x) => Ratreal(uminus_rat(x))
}

def zero_rat: rat = Frct((zero_int, one_int))

def zero_reala: real = Ratreal(zero_rat)

def less_rat(p: rat, q: rat): Boolean =
  {
    val a: (int, int) = quotient_of(p)
    val (aa, c): (int, int) = a
    val b: (int, int) = quotient_of(q)
    val (ba, d): (int, int) = b;
    less_int(times_int(aa, d), times_int(c, ba))
  }

def less_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => less_rat(x, y)
}

def abs_reala(a: real): real =
  (if (less_real(a, zero_reala)) uminus_reala(a) else a)

trait abs[A] {
  val `foveSIMM.abs`: A => A
}
def abs[A](a: A)(implicit A: abs[A]): A = A.`foveSIMM.abs`(a)
object abs {
  implicit def `foveSIMM.abs_real`: abs[real] = new abs[real] {
    val `foveSIMM.abs` = (a: real) => abs_reala(a)
  }
}

def one_rat: rat = Frct((one_int, one_int))

def one_reala: real = Ratreal(one_rat)

trait one[A] {
  val `foveSIMM.one`: A
}
def one[A](implicit A: one[A]): A = A.`foveSIMM.one`
object one {
  implicit def `foveSIMM.one_real`: one[real] = new one[real] {
    val `foveSIMM.one` = one_reala
  }
}

def equal_prod[A : equal, B : equal](x0: (A, B), x1: (A, B)): Boolean = (x0, x1)
  match {
  case ((x1, x2), (y1, y2)) => eq[A](x1, y1) && eq[B](x2, y2)
}

def equal_rat(a: rat, b: rat): Boolean =
  equal_prod[int, int](quotient_of(a), quotient_of(b))

def equal_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => equal_rat(x, y)
}

def sgn_reala(a: real): real =
  (if (equal_real(a, zero_reala)) zero_reala
    else (if (less_real(zero_reala, a)) one_reala else uminus_reala(one_reala)))

trait sgn[A] {
  val `foveSIMM.sgn`: A => A
}
def sgn[A](a: A)(implicit A: sgn[A]): A = A.`foveSIMM.sgn`(a)
object sgn {
  implicit def `foveSIMM.sgn_real`: sgn[real] = new sgn[real] {
    val `foveSIMM.sgn` = (a: real) => sgn_reala(a)
  }
}

def minus_int(k: int, l: int): int =
  int_of_integer(integer_of_int(k) - integer_of_int(l))

def minus_rat(p: rat, q: rat): rat =
  Frct({
         val a: (int, int) = quotient_of(p)
         val (aa, c): (int, int) = a
         val b: (int, int) = quotient_of(q)
         val (ba, d): (int, int) = b;
         normalize((minus_int(times_int(aa, d), times_int(ba, c)),
                     times_int(c, d)))
       })

def minus_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(minus_rat(x, y))
}

def plus_int(k: int, l: int): int =
  int_of_integer(integer_of_int(k) + integer_of_int(l))

def plus_rat(p: rat, q: rat): rat =
  Frct({
         val a: (int, int) = quotient_of(p)
         val (aa, c): (int, int) = a
         val b: (int, int) = quotient_of(q)
         val (ba, d): (int, int) = b;
         normalize((plus_int(times_int(aa, d), times_int(ba, c)),
                     times_int(c, d)))
       })

def plus_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(plus_rat(x, y))
}

trait uminus[A] {
  val `foveSIMM.uminus`: A => A
}
def uminus[A](a: A)(implicit A: uminus[A]): A = A.`foveSIMM.uminus`(a)
object uminus {
  implicit def `foveSIMM.uminus_real`: uminus[real] = new uminus[real] {
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
  }
}

trait minus[A] {
  val `foveSIMM.minus`: (A, A) => A
}
def minus[A](a: A, b: A)(implicit A: minus[A]): A = A.`foveSIMM.minus`(a, b)
object minus {
  implicit def `foveSIMM.minus_real`: minus[real] = new minus[real] {
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
  }
}

trait zero[A] {
  val `foveSIMM.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`foveSIMM.zero`
object zero {
  implicit def `foveSIMM.zero_real`: zero[real] = new zero[real] {
    val `foveSIMM.zero` = zero_reala
  }
}

trait plus[A] {
  val `foveSIMM.plus`: (A, A) => A
}
def plus[A](a: A, b: A)(implicit A: plus[A]): A = A.`foveSIMM.plus`(a, b)
object plus {
  implicit def `foveSIMM.plus_real`: plus[real] = new plus[real] {
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait semigroup_add[A] extends plus[A] {
}
object semigroup_add {
  implicit def `foveSIMM.semigroup_add_real`: semigroup_add[real] = new
    semigroup_add[real] {
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait cancel_semigroup_add[A] extends semigroup_add[A] {
}
object cancel_semigroup_add {
  implicit def `foveSIMM.cancel_semigroup_add_real`: cancel_semigroup_add[real]
    = new cancel_semigroup_add[real] {
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ab_semigroup_add[A] extends semigroup_add[A] {
}
object ab_semigroup_add {
  implicit def `foveSIMM.ab_semigroup_add_real`: ab_semigroup_add[real] = new
    ab_semigroup_add[real] {
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait cancel_ab_semigroup_add[A]
  extends ab_semigroup_add[A] with cancel_semigroup_add[A] with minus[A] {
}
object cancel_ab_semigroup_add {
  implicit def
    `foveSIMM.cancel_ab_semigroup_add_real`: cancel_ab_semigroup_add[real] = new
    cancel_ab_semigroup_add[real] {
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait monoid_add[A] extends semigroup_add[A] with zero[A] {
}
object monoid_add {
  implicit def `foveSIMM.monoid_add_real`: monoid_add[real] = new
    monoid_add[real] {
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait comm_monoid_add[A] extends ab_semigroup_add[A] with monoid_add[A] {
}
object comm_monoid_add {
  implicit def `foveSIMM.comm_monoid_add_real`: comm_monoid_add[real] = new
    comm_monoid_add[real] {
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait cancel_comm_monoid_add[A]
  extends cancel_ab_semigroup_add[A] with comm_monoid_add[A] {
}
object cancel_comm_monoid_add {
  implicit def
    `foveSIMM.cancel_comm_monoid_add_real`: cancel_comm_monoid_add[real] = new
    cancel_comm_monoid_add[real] {
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait mult_zero[A] extends times[A] with zero[A] {
}
object mult_zero {
  implicit def `foveSIMM.mult_zero_real`: mult_zero[real] = new mult_zero[real]
    {
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
  }
}

trait semigroup_mult[A] extends times[A] {
}
object semigroup_mult {
  implicit def `foveSIMM.semigroup_mult_real`: semigroup_mult[real] = new
    semigroup_mult[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
  }
}

trait semiring[A] extends ab_semigroup_add[A] with semigroup_mult[A] {
}
object semiring {
  implicit def `foveSIMM.semiring_real`: semiring[real] = new semiring[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait semiring_0[A]
  extends comm_monoid_add[A] with mult_zero[A] with semiring[A] {
}
object semiring_0 {
  implicit def `foveSIMM.semiring_0_real`: semiring_0[real] = new
    semiring_0[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait semiring_0_cancel[A] extends cancel_comm_monoid_add[A] with semiring_0[A]
  {
}
object semiring_0_cancel {
  implicit def `foveSIMM.semiring_0_cancel_real`: semiring_0_cancel[real] = new
    semiring_0_cancel[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ab_semigroup_mult[A] extends semigroup_mult[A] {
}
object ab_semigroup_mult {
  implicit def `foveSIMM.ab_semigroup_mult_real`: ab_semigroup_mult[real] = new
    ab_semigroup_mult[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
  }
}

trait comm_semiring[A] extends ab_semigroup_mult[A] with semiring[A] {
}
object comm_semiring {
  implicit def `foveSIMM.comm_semiring_real`: comm_semiring[real] = new
    comm_semiring[real] {
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
  }
}

trait comm_semiring_0[A] extends comm_semiring[A] with semiring_0[A] {
}
object comm_semiring_0 {
  implicit def `foveSIMM.comm_semiring_0_real`: comm_semiring_0[real] = new
    comm_semiring_0[real] {
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
  }
}

trait comm_semiring_0_cancel[A]
  extends comm_semiring_0[A] with semiring_0_cancel[A] {
}
object comm_semiring_0_cancel {
  implicit def
    `foveSIMM.comm_semiring_0_cancel_real`: comm_semiring_0_cancel[real] = new
    comm_semiring_0_cancel[real] {
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
  }
}

trait power[A] extends one[A] with times[A] {
}
object power {
  implicit def `foveSIMM.power_real`: power[real] = new power[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.one` = one_reala
  }
}

trait monoid_mult[A] extends semigroup_mult[A] with power[A] {
}
object monoid_mult {
  implicit def `foveSIMM.monoid_mult_real`: monoid_mult[real] = new
    monoid_mult[real] {
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
  }
}

trait numeral[A] extends one[A] with semigroup_add[A] {
}
object numeral {
  implicit def `foveSIMM.numeral_real`: numeral[real] = new numeral[real] {
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
    val `foveSIMM.one` = one_reala
  }
}

trait semiring_numeral[A]
  extends monoid_mult[A] with numeral[A] with semiring[A] {
}
object semiring_numeral {
  implicit def `foveSIMM.semiring_numeral_real`: semiring_numeral[real] = new
    semiring_numeral[real] {
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
  }
}

trait zero_neq_one[A] extends one[A] with zero[A] {
}
object zero_neq_one {
  implicit def `foveSIMM.zero_neq_one_real`: zero_neq_one[real] = new
    zero_neq_one[real] {
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.one` = one_reala
  }
}

trait semiring_1[A]
  extends semiring_numeral[A] with semiring_0[A] with zero_neq_one[A] {
}
object semiring_1 {
  implicit def `foveSIMM.semiring_1_real`: semiring_1[real] = new
    semiring_1[real] {
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait semiring_1_cancel[A] extends semiring_0_cancel[A] with semiring_1[A] {
}
object semiring_1_cancel {
  implicit def `foveSIMM.semiring_1_cancel_real`: semiring_1_cancel[real] = new
    semiring_1_cancel[real] {
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait comm_monoid_mult[A]
  extends ab_semigroup_mult[A] with monoid_mult[A] with dvd[A] {
}
object comm_monoid_mult {
  implicit def `foveSIMM.comm_monoid_mult_real`: comm_monoid_mult[real] = new
    comm_monoid_mult[real] {
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
  }
}

trait comm_semiring_1[A]
  extends comm_monoid_mult[A] with comm_semiring_0[A] with semiring_1[A] {
}
object comm_semiring_1 {
  implicit def `foveSIMM.comm_semiring_1_real`: comm_semiring_1[real] = new
    comm_semiring_1[real] {
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
  }
}

trait comm_semiring_1_cancel[A]
  extends comm_semiring_0_cancel[A] with comm_semiring_1[A] with
    semiring_1_cancel[A]
  {
}
object comm_semiring_1_cancel {
  implicit def
    `foveSIMM.comm_semiring_1_cancel_real`: comm_semiring_1_cancel[real] = new
    comm_semiring_1_cancel[real] {
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait comm_semiring_1_cancel_crossproduct[A] extends comm_semiring_1_cancel[A] {
}
object comm_semiring_1_cancel_crossproduct {
  implicit def
    `foveSIMM.comm_semiring_1_cancel_crossproduct_real`:
      comm_semiring_1_cancel_crossproduct[real]
    = new comm_semiring_1_cancel_crossproduct[real] {
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait semiring_no_zero_divisors[A] extends semiring_0[A] {
}
object semiring_no_zero_divisors {
  implicit def
    `foveSIMM.semiring_no_zero_divisors_real`: semiring_no_zero_divisors[real] =
    new semiring_no_zero_divisors[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait semiring_1_no_zero_divisors[A]
  extends semiring_1[A] with semiring_no_zero_divisors[A] {
}
object semiring_1_no_zero_divisors {
  implicit def
    `foveSIMM.semiring_1_no_zero_divisors_real`:
      semiring_1_no_zero_divisors[real]
    = new semiring_1_no_zero_divisors[real] {
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait semiring_no_zero_divisors_cancel[A] extends semiring_no_zero_divisors[A] {
}
object semiring_no_zero_divisors_cancel {
  implicit def
    `foveSIMM.semiring_no_zero_divisors_cancel_real`:
      semiring_no_zero_divisors_cancel[real]
    = new semiring_no_zero_divisors_cancel[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait group_add[A]
  extends cancel_semigroup_add[A] with minus[A] with monoid_add[A] with
    uminus[A]
  {
}
object group_add {
  implicit def `foveSIMM.group_add_real`: group_add[real] = new group_add[real]
    {
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ab_group_add[A] extends cancel_comm_monoid_add[A] with group_add[A] {
}
object ab_group_add {
  implicit def `foveSIMM.ab_group_add_real`: ab_group_add[real] = new
    ab_group_add[real] {
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ring[A] extends ab_group_add[A] with semiring_0_cancel[A] {
}
object ring {
  implicit def `foveSIMM.ring_real`: ring[real] = new ring[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ring_no_zero_divisors[A]
  extends ring[A] with semiring_no_zero_divisors_cancel[A] {
}
object ring_no_zero_divisors {
  implicit def
    `foveSIMM.ring_no_zero_divisors_real`: ring_no_zero_divisors[real] = new
    ring_no_zero_divisors[real] {
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait neg_numeral[A] extends group_add[A] with numeral[A] {
}
object neg_numeral {
  implicit def `foveSIMM.neg_numeral_real`: neg_numeral[real] = new
    neg_numeral[real] {
    val `foveSIMM.one` = one_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ring_1[A] extends neg_numeral[A] with ring[A] with semiring_1_cancel[A] {
}
object ring_1 {
  implicit def `foveSIMM.ring_1_real`: ring_1[real] = new ring_1[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ring_1_no_zero_divisors[A]
  extends ring_1[A] with ring_no_zero_divisors[A] with
    semiring_1_no_zero_divisors[A]
  {
}
object ring_1_no_zero_divisors {
  implicit def
    `foveSIMM.ring_1_no_zero_divisors_real`: ring_1_no_zero_divisors[real] = new
    ring_1_no_zero_divisors[real] {
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait comm_ring[A] extends comm_semiring_0_cancel[A] with ring[A] {
}
object comm_ring {
  implicit def `foveSIMM.comm_ring_real`: comm_ring[real] = new comm_ring[real]
    {
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait comm_ring_1[A]
  extends comm_ring[A] with comm_semiring_1_cancel[A] with ring_1[A] {
}
object comm_ring_1 {
  implicit def `foveSIMM.comm_ring_1_real`: comm_ring_1[real] = new
    comm_ring_1[real] {
    val `foveSIMM.one` = one_reala
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait semidom[A]
  extends comm_semiring_1_cancel[A] with semiring_1_no_zero_divisors[A] {
}
object semidom {
  implicit def `foveSIMM.semidom_real`: semidom[real] = new semidom[real] {
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait idom[A]
  extends comm_ring_1[A] with ring_1_no_zero_divisors[A] with semidom[A] with
    comm_semiring_1_cancel_crossproduct[A]
  {
}
object idom {
  implicit def `foveSIMM.idom_real`: idom[real] = new idom[real] {
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

def sgn_int(i: int): int =
  (if (equal_inta(i, zero_int)) zero_int
    else (if (less_int(zero_int, i)) one_int else uminus_int(one_int)))

def abs_int(i: int): int = (if (less_int(i, zero_int)) uminus_int(i) else i)

def inverse_rat(p: rat): rat =
  Frct({
         val a: (int, int) = quotient_of(p)
         val (aa, b): (int, int) = a;
         (if (equal_inta(aa, zero_int)) (zero_int, one_int)
           else (times_int(sgn_int(aa), b), abs_int(aa)))
       })

def inverse_reala(x0: real): real = x0 match {
  case Ratreal(x) => Ratreal(inverse_rat(x))
}

def divide_rat(p: rat, q: rat): rat =
  Frct({
         val a: (int, int) = quotient_of(p)
         val (aa, c): (int, int) = a
         val b: (int, int) = quotient_of(q)
         val (ba, d): (int, int) = b;
         normalize((times_int(aa, d), times_int(c, ba)))
       })

def divide_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(divide_rat(x, y))
}

trait divide[A] {
  val `foveSIMM.divide`: (A, A) => A
}
def divide[A](a: A, b: A)(implicit A: divide[A]): A = A.`foveSIMM.divide`(a, b)
object divide {
  implicit def `foveSIMM.divide_real`: divide[real] = new divide[real] {
    val `foveSIMM.divide` = (a: real, b: real) => divide_reala(a, b)
  }
}

trait inverse[A] extends divide[A] {
  val `foveSIMM.inverse`: A => A
}
def inverse[A](a: A)(implicit A: inverse[A]): A = A.`foveSIMM.inverse`(a)
object inverse {
  implicit def `foveSIMM.inverse_real`: inverse[real] = new inverse[real] {
    val `foveSIMM.inverse` = (a: real) => inverse_reala(a)
    val `foveSIMM.divide` = (a: real, b: real) => divide_reala(a, b)
  }
}

trait division_ring[A] extends inverse[A] with ring_1_no_zero_divisors[A] {
}
object division_ring {
  implicit def `foveSIMM.division_ring_real`: division_ring[real] = new
    division_ring[real] {
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
    val `foveSIMM.inverse` = (a: real) => inverse_reala(a)
    val `foveSIMM.divide` = (a: real, b: real) => divide_reala(a, b)
  }
}

trait semidom_divide[A]
  extends divide[A] with semidom[A] with semiring_no_zero_divisors_cancel[A] {
}
object semidom_divide {
  implicit def `foveSIMM.semidom_divide_real`: semidom_divide[real] = new
    semidom_divide[real] {
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
    val `foveSIMM.divide` = (a: real, b: real) => divide_reala(a, b)
  }
}

trait idom_divide[A] extends idom[A] with semidom_divide[A] {
}
object idom_divide {
  implicit def `foveSIMM.idom_divide_real`: idom_divide[real] = new
    idom_divide[real] {
    val `foveSIMM.divide` = (a: real, b: real) => divide_reala(a, b)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait field[A] extends division_ring[A] with idom_divide[A] {
}
object field {
  implicit def `foveSIMM.field_real`: field[real] = new field[real] {
    val `foveSIMM.inverse` = (a: real) => inverse_reala(a)
    val `foveSIMM.divide` = (a: real, b: real) => divide_reala(a, b)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

def less_eq_int(k: int, l: int): Boolean =
  integer_of_int(k) <= integer_of_int(l)

def less_eq_rat(p: rat, q: rat): Boolean =
  {
    val a: (int, int) = quotient_of(p)
    val (aa, c): (int, int) = a
    val b: (int, int) = quotient_of(q)
    val (ba, d): (int, int) = b;
    less_eq_int(times_int(aa, d), times_int(c, ba))
  }

def less_eq_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => less_eq_rat(x, y)
}

trait ord[A] {
  val `foveSIMM.less_eq`: (A, A) => Boolean
  val `foveSIMM.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`foveSIMM.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`foveSIMM.less`(a, b)
object ord {
  implicit def `foveSIMM.ord_real`: ord[real] = new ord[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
  }
}

trait abs_if[A]
  extends abs[A] with minus[A] with uminus[A] with zero[A] with ord[A] {
}
object abs_if {
  implicit def `foveSIMM.abs_if_real`: abs_if[real] = new abs_if[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.abs` = (a: real) => abs_reala(a)
  }
}

trait semiring_char_0[A] extends semiring_1[A] {
}
object semiring_char_0 {
  implicit def `foveSIMM.semiring_char_0_real`: semiring_char_0[real] = new
    semiring_char_0[real] {
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ring_char_0[A] extends semiring_char_0[A] with ring_1[A] {
}
object ring_char_0 {
  implicit def `foveSIMM.ring_char_0_real`: ring_char_0[real] = new
    ring_char_0[real] {
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait preorder[A] extends ord[A] {
}
object preorder {
  implicit def `foveSIMM.preorder_real`: preorder[real] = new preorder[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
  }
}

trait order[A] extends preorder[A] {
}
object order {
  implicit def `foveSIMM.order_real`: order[real] = new order[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
  }
}

trait no_bot[A] extends order[A] {
}
object no_bot {
  implicit def `foveSIMM.no_bot_real`: no_bot[real] = new no_bot[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
  }
}

trait no_top[A] extends order[A] {
}
object no_top {
  implicit def `foveSIMM.no_top_real`: no_top[real] = new no_top[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
  }
}

trait linorder[A] extends order[A] {
}
object linorder {
  implicit def `foveSIMM.linorder_real`: linorder[real] = new linorder[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
  }
}

trait idom_abs_sgn[A] extends abs[A] with sgn[A] with idom[A] {
}
object idom_abs_sgn {
  implicit def `foveSIMM.idom_abs_sgn_real`: idom_abs_sgn[real] = new
    idom_abs_sgn[real] {
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
    val `foveSIMM.sgn` = (a: real) => sgn_reala(a)
    val `foveSIMM.abs` = (a: real) => abs_reala(a)
  }
}

trait ordered_ab_semigroup_add[A] extends ab_semigroup_add[A] with order[A] {
}
object ordered_ab_semigroup_add {
  implicit def
    `foveSIMM.ordered_ab_semigroup_add_real`: ordered_ab_semigroup_add[real] =
    new ordered_ab_semigroup_add[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ordered_comm_monoid_add[A]
  extends comm_monoid_add[A] with ordered_ab_semigroup_add[A] {
}
object ordered_comm_monoid_add {
  implicit def
    `foveSIMM.ordered_comm_monoid_add_real`: ordered_comm_monoid_add[real] = new
    ordered_comm_monoid_add[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ordered_semiring[A] extends ordered_comm_monoid_add[A] with semiring[A] {
}
object ordered_semiring {
  implicit def `foveSIMM.ordered_semiring_real`: ordered_semiring[real] = new
    ordered_semiring[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ordered_semiring_0[A] extends ordered_semiring[A] with semiring_0[A] {
}
object ordered_semiring_0 {
  implicit def `foveSIMM.ordered_semiring_0_real`: ordered_semiring_0[real] =
    new ordered_semiring_0[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ordered_cancel_semiring[A]
  extends ordered_semiring_0[A] with semiring_0_cancel[A] {
}
object ordered_cancel_semiring {
  implicit def
    `foveSIMM.ordered_cancel_semiring_real`: ordered_cancel_semiring[real] = new
    ordered_cancel_semiring[real] {
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait strict_ordered_ab_semigroup_add[A] extends ordered_ab_semigroup_add[A] {
}
object strict_ordered_ab_semigroup_add {
  implicit def
    `foveSIMM.strict_ordered_ab_semigroup_add_real`:
      strict_ordered_ab_semigroup_add[real]
    = new strict_ordered_ab_semigroup_add[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ordered_cancel_ab_semigroup_add[A]
  extends cancel_ab_semigroup_add[A] with strict_ordered_ab_semigroup_add[A] {
}
object ordered_cancel_ab_semigroup_add {
  implicit def
    `foveSIMM.ordered_cancel_ab_semigroup_add_real`:
      ordered_cancel_ab_semigroup_add[real]
    = new ordered_cancel_ab_semigroup_add[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ordered_ab_semigroup_add_imp_le[A]
  extends ordered_cancel_ab_semigroup_add[A] {
}
object ordered_ab_semigroup_add_imp_le {
  implicit def
    `foveSIMM.ordered_ab_semigroup_add_imp_le_real`:
      ordered_ab_semigroup_add_imp_le[real]
    = new ordered_ab_semigroup_add_imp_le[real] {
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait strict_ordered_comm_monoid_add[A]
  extends comm_monoid_add[A] with strict_ordered_ab_semigroup_add[A] {
}
object strict_ordered_comm_monoid_add {
  implicit def
    `foveSIMM.strict_ordered_comm_monoid_add_real`:
      strict_ordered_comm_monoid_add[real]
    = new strict_ordered_comm_monoid_add[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ordered_cancel_comm_monoid_add[A]
  extends ordered_cancel_ab_semigroup_add[A] with ordered_comm_monoid_add[A]
    with strict_ordered_comm_monoid_add[A]
  {
}
object ordered_cancel_comm_monoid_add {
  implicit def
    `foveSIMM.ordered_cancel_comm_monoid_add_real`:
      ordered_cancel_comm_monoid_add[real]
    = new ordered_cancel_comm_monoid_add[real] {
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ordered_ab_semigroup_monoid_add_imp_le[A]
  extends cancel_comm_monoid_add[A] with ordered_ab_semigroup_add_imp_le[A] with
    ordered_cancel_comm_monoid_add[A]
  {
}
object ordered_ab_semigroup_monoid_add_imp_le {
  implicit def
    `foveSIMM.ordered_ab_semigroup_monoid_add_imp_le_real`:
      ordered_ab_semigroup_monoid_add_imp_le[real]
    = new ordered_ab_semigroup_monoid_add_imp_le[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ordered_ab_group_add[A]
  extends ab_group_add[A] with ordered_ab_semigroup_monoid_add_imp_le[A] {
}
object ordered_ab_group_add {
  implicit def `foveSIMM.ordered_ab_group_add_real`: ordered_ab_group_add[real]
    = new ordered_ab_group_add[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ordered_ring[A]
  extends ordered_ab_group_add[A] with ordered_cancel_semiring[A] with ring[A] {
}
object ordered_ring {
  implicit def `foveSIMM.ordered_ring_real`: ordered_ring[real] = new
    ordered_ring[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait field_char_0[A] extends field[A] with ring_char_0[A] {
}
object field_char_0 {
  implicit def `foveSIMM.field_char_0_real`: field_char_0[real] = new
    field_char_0[real] {
    val `foveSIMM.inverse` = (a: real) => inverse_reala(a)
    val `foveSIMM.divide` = (a: real, b: real) => divide_reala(a, b)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait zero_less_one[A] extends one[A] with zero[A] with order[A] {
}
object zero_less_one {
  implicit def `foveSIMM.zero_less_one_real`: zero_less_one[real] = new
    zero_less_one[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.one` = one_reala
  }
}

trait field_abs_sgn[A] extends field[A] with idom_abs_sgn[A] {
}
object field_abs_sgn {
  implicit def `foveSIMM.field_abs_sgn_real`: field_abs_sgn[real] = new
    field_abs_sgn[real] {
    val `foveSIMM.abs` = (a: real) => abs_reala(a)
    val `foveSIMM.sgn` = (a: real) => sgn_reala(a)
    val `foveSIMM.inverse` = (a: real) => inverse_reala(a)
    val `foveSIMM.divide` = (a: real, b: real) => divide_reala(a, b)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait dense_order[A] extends order[A] {
}
object dense_order {
  implicit def `foveSIMM.dense_order_real`: dense_order[real] = new
    dense_order[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
  }
}

trait linordered_ab_semigroup_add[A]
  extends ordered_ab_semigroup_add[A] with linorder[A] {
}
object linordered_ab_semigroup_add {
  implicit def
    `foveSIMM.linordered_ab_semigroup_add_real`:
      linordered_ab_semigroup_add[real]
    = new linordered_ab_semigroup_add[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait linordered_cancel_ab_semigroup_add[A]
  extends linordered_ab_semigroup_add[A] with ordered_ab_semigroup_add_imp_le[A]
  {
}
object linordered_cancel_ab_semigroup_add {
  implicit def
    `foveSIMM.linordered_cancel_ab_semigroup_add_real`:
      linordered_cancel_ab_semigroup_add[real]
    = new linordered_cancel_ab_semigroup_add[real] {
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait linordered_semiring[A]
  extends linordered_cancel_ab_semigroup_add[A] with
    ordered_ab_semigroup_monoid_add_imp_le[A] with ordered_cancel_semiring[A]
  {
}
object linordered_semiring {
  implicit def `foveSIMM.linordered_semiring_real`: linordered_semiring[real] =
    new linordered_semiring[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait linordered_semiring_strict[A] extends linordered_semiring[A] {
}
object linordered_semiring_strict {
  implicit def
    `foveSIMM.linordered_semiring_strict_real`: linordered_semiring_strict[real]
    = new linordered_semiring_strict[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait linordered_semiring_1[A]
  extends linordered_semiring[A] with semiring_1[A] with zero_less_one[A] {
}
object linordered_semiring_1 {
  implicit def
    `foveSIMM.linordered_semiring_1_real`: linordered_semiring_1[real] = new
    linordered_semiring_1[real] {
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait linordered_semiring_1_strict[A]
  extends linordered_semiring_1[A] with linordered_semiring_strict[A] {
}
object linordered_semiring_1_strict {
  implicit def
    `foveSIMM.linordered_semiring_1_strict_real`:
      linordered_semiring_1_strict[real]
    = new linordered_semiring_1_strict[real] {
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ordered_ab_group_add_abs[A] extends abs[A] with ordered_ab_group_add[A] {
}
object ordered_ab_group_add_abs {
  implicit def
    `foveSIMM.ordered_ab_group_add_abs_real`: ordered_ab_group_add_abs[real] =
    new ordered_ab_group_add_abs[real] {
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
    val `foveSIMM.abs` = (a: real) => abs_reala(a)
  }
}

trait linordered_ab_group_add[A]
  extends linordered_cancel_ab_semigroup_add[A] with ordered_ab_group_add[A] {
}
object linordered_ab_group_add {
  implicit def
    `foveSIMM.linordered_ab_group_add_real`: linordered_ab_group_add[real] = new
    linordered_ab_group_add[real] {
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait linordered_ring[A]
  extends linordered_ab_group_add[A] with ordered_ab_group_add_abs[A] with
    abs_if[A] with linordered_semiring[A] with ordered_ring[A]
  {
}
object linordered_ring {
  implicit def `foveSIMM.linordered_ring_real`: linordered_ring[real] = new
    linordered_ring[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.abs` = (a: real) => abs_reala(a)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait linordered_ring_strict[A]
  extends linordered_ring[A] with linordered_semiring_strict[A] with
    ring_no_zero_divisors[A]
  {
}
object linordered_ring_strict {
  implicit def
    `foveSIMM.linordered_ring_strict_real`: linordered_ring_strict[real] = new
    linordered_ring_strict[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.abs` = (a: real) => abs_reala(a)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ordered_comm_semiring[A]
  extends comm_semiring_0[A] with ordered_semiring[A] {
}
object ordered_comm_semiring {
  implicit def
    `foveSIMM.ordered_comm_semiring_real`: ordered_comm_semiring[real] = new
    ordered_comm_semiring[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
  }
}

trait ordered_cancel_comm_semiring[A]
  extends comm_semiring_0_cancel[A] with ordered_cancel_semiring[A] with
    ordered_comm_semiring[A]
  {
}
object ordered_cancel_comm_semiring {
  implicit def
    `foveSIMM.ordered_cancel_comm_semiring_real`:
      ordered_cancel_comm_semiring[real]
    = new ordered_cancel_comm_semiring[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait linordered_comm_semiring_strict[A]
  extends linordered_semiring_strict[A] with ordered_cancel_comm_semiring[A] {
}
object linordered_comm_semiring_strict {
  implicit def
    `foveSIMM.linordered_comm_semiring_strict_real`:
      linordered_comm_semiring_strict[real]
    = new linordered_comm_semiring_strict[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait linordered_nonzero_semiring[A]
  extends semiring_char_0[A] with linorder[A] with comm_semiring_1[A] with
    ordered_comm_semiring[A] with zero_less_one[A]
  {
}
object linordered_nonzero_semiring {
  implicit def
    `foveSIMM.linordered_nonzero_semiring_real`:
      linordered_nonzero_semiring[real]
    = new linordered_nonzero_semiring[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait linordered_semidom[A]
  extends linordered_comm_semiring_strict[A] with linordered_nonzero_semiring[A]
    with semidom[A]
  {
}
object linordered_semidom {
  implicit def `foveSIMM.linordered_semidom_real`: linordered_semidom[real] =
    new linordered_semidom[real] {
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ordered_comm_ring[A]
  extends comm_ring[A] with ordered_cancel_comm_semiring[A] with ordered_ring[A]
  {
}
object ordered_comm_ring {
  implicit def `foveSIMM.ordered_comm_ring_real`: ordered_comm_ring[real] = new
    ordered_comm_ring[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait ordered_ring_abs[A]
  extends ordered_ab_group_add_abs[A] with ordered_ring[A] {
}
object ordered_ring_abs {
  implicit def `foveSIMM.ordered_ring_abs_real`: ordered_ring_abs[real] = new
    ordered_ring_abs[real] {
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.abs` = (a: real) => abs_reala(a)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait linordered_idom[A]
  extends ring_char_0[A] with idom_abs_sgn[A] with linordered_ring_strict[A]
    with linordered_semidom[A] with linordered_semiring_1_strict[A] with
    ordered_comm_ring[A] with ordered_ring_abs[A]
  {
}
object linordered_idom {
  implicit def `foveSIMM.linordered_idom_real`: linordered_idom[real] = new
    linordered_idom[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.abs` = (a: real) => abs_reala(a)
    val `foveSIMM.sgn` = (a: real) => sgn_reala(a)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait dense_linorder[A] extends dense_order[A] with linorder[A] {
}
object dense_linorder {
  implicit def `foveSIMM.dense_linorder_real`: dense_linorder[real] = new
    dense_linorder[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
  }
}

trait unbounded_dense_linorder[A]
  extends dense_linorder[A] with no_bot[A] with no_top[A] {
}
object unbounded_dense_linorder {
  implicit def
    `foveSIMM.unbounded_dense_linorder_real`: unbounded_dense_linorder[real] =
    new unbounded_dense_linorder[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
  }
}

trait linordered_field[A]
  extends field_abs_sgn[A] with field_char_0[A] with unbounded_dense_linorder[A]
    with linordered_idom[A]
  {
}
object linordered_field {
  implicit def `foveSIMM.linordered_field_real`: linordered_field[real] = new
    linordered_field[real] {
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.abs` = (a: real) => abs_reala(a)
    val `foveSIMM.sgn` = (a: real) => sgn_reala(a)
    val `foveSIMM.inverse` = (a: real) => inverse_reala(a)
    val `foveSIMM.divide` = (a: real, b: real) => divide_reala(a, b)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait archimedean_field[A] extends linordered_field[A] {
}
object archimedean_field {
  implicit def `foveSIMM.archimedean_field_real`: archimedean_field[real] = new
    archimedean_field[real] {
    val `foveSIMM.inverse` = (a: real) => inverse_reala(a)
    val `foveSIMM.divide` = (a: real, b: real) => divide_reala(a, b)
    val `foveSIMM.sgn` = (a: real) => sgn_reala(a)
    val `foveSIMM.abs` = (a: real) => abs_reala(a)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

trait floor_ceiling[A] extends archimedean_field[A] {
  val `foveSIMM.floor`: A => int
}
def floor[A](a: A)(implicit A: floor_ceiling[A]): int = A.`foveSIMM.floor`(a)
object floor_ceiling {
  implicit def `foveSIMM.floor_ceiling_real`: floor_ceiling[real] = new
    floor_ceiling[real] {
    val `foveSIMM.floor` = (a: real) => floor_real(a)
    val `foveSIMM.inverse` = (a: real) => inverse_reala(a)
    val `foveSIMM.divide` = (a: real, b: real) => divide_reala(a, b)
    val `foveSIMM.sgn` = (a: real) => sgn_reala(a)
    val `foveSIMM.abs` = (a: real) => abs_reala(a)
    val `foveSIMM.uminus` = (a: real) => uminus_reala(a)
    val `foveSIMM.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `foveSIMM.less` = (a: real, b: real) => less_real(a, b)
    val `foveSIMM.one` = one_reala
    val `foveSIMM.times` = (a: real, b: real) => times_reala(a, b)
    val `foveSIMM.zero` = zero_reala
    val `foveSIMM.minus` = (a: real, b: real) => minus_reala(a, b)
    val `foveSIMM.plus` = (a: real, b: real) => plus_reala(a, b)
  }
}

def floor_rat(p: rat): int = {
                               val a: (int, int) = quotient_of(p)
                               val (aa, b): (int, int) = a;
                               divide_int(aa, b)
                             }

def floor_real(x0: real): int = x0 match {
  case Ratreal(x) => floor_rat(x)
}

def equal_bool(p: Boolean, pa: Boolean): Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

abstract sealed class char
final case class
  Char(a: Boolean, b: Boolean, c: Boolean, d: Boolean, e: Boolean, f: Boolean,
        g: Boolean, h: Boolean)
  extends char

def equal_chara(x0: char, x1: char): Boolean = (x0, x1) match {
  case (Char(x1, x2, x3, x4, x5, x6, x7, x8),
         Char(y1, y2, y3, y4, y5, y6, y7, y8))
    => equal_bool(x1, y1) &&
         (equal_bool(x2, y2) &&
           (equal_bool(x3, y3) &&
             (equal_bool(x4, y4) &&
               (equal_bool(x5, y5) &&
                 (equal_bool(x6, y6) &&
                   (equal_bool(x7, y7) && equal_bool(x8, y8)))))))
}

abstract sealed class nat
final case class zero_nat() extends nat
final case class Suc(a: nat) extends nat

abstract sealed class risk_factor_ext[A]
final case class
  risk_factor_exta[A](a: List[char], b: List[char], c: List[char],
                       d: List[char], e: real, f: A)
  extends risk_factor_ext[A]

abstract sealed class fx_rate_shock_ext[A]
final case class
  fx_rate_shock_exta[A](a: List[char], b: nat, c: List[real], d: A)
  extends fx_rate_shock_ext[A]

abstract sealed class risk_factor_shock_ext[A]
final case class risk_factor_shock_exta[A](a: List[char], b: List[real], c: A)
  extends risk_factor_shock_ext[A]

abstract sealed class portfolio_derivative_ext[A]
final case class
  portfolio_derivative_exta[A](a: List[char], b: int, c: nat, d: A)
  extends portfolio_derivative_ext[A]

abstract sealed class risk_factor_base_level_ext[A]
final case class risk_factor_base_level_exta[A](a: List[char], b: real, c: A)
  extends risk_factor_base_level_ext[A]

abstract sealed class portfolio_initial_margin_ext[A]
final case class
  portfolio_initial_margin_exta[A](a: List[char], b: int, c: nat, d: A)
  extends portfolio_initial_margin_ext[A]

abstract sealed class portfolio_variation_margin_ext[A]
final case class
  portfolio_variation_margin_exta[A](a: List[char], b: int, c: nat, d: A)
  extends portfolio_variation_margin_ext[A]

def id[A]: A => A = ((x: A) => x)

def plus_nat(x0: nat, n: nat): nat = (x0, n) match {
  case (Suc(m), n) => plus_nat(m, Suc(n))
  case (zero_nat(), n) => n
}

def one_nat: nat = Suc(zero_nat())

def nat_of_integer(k: BigInt): nat =
  (if (k <= BigInt(0)) zero_nat()
    else {
           val (l, j): (BigInt, BigInt) = divmod_integer(k, BigInt(2))
           val la: nat = nat_of_integer(l)
           val lb: nat = plus_nat(la, la);
           (if (j == BigInt(0)) lb else plus_nat(lb, one_nat))
         })

def nat: int => nat =
  comp[BigInt, nat,
        int](((a: BigInt) => nat_of_integer(a)),
              ((a: int) => integer_of_int(a)))

def nth[A](x0: List[A], x1: nat): A = (x0, x1) match {
  case (x :: xs, Suc(n)) => nth[A](xs, n)
  case (x :: xs, zero_nat()) => x
}

def nulla[A](x0: List[A]): Boolean = x0 match {
  case Nil => true
  case x :: xs => false
}

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => id[B]
  case (f, x :: xs) => comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def of_int(a: int): rat = Frct((a, one_int))

def member[A : equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => eq[A](x, y) || member[A](xs, y)
}

def nat_of_num(x0: num): nat = x0 match {
  case Bit1(n) => {
                    val m: nat = nat_of_num(n);
                    Suc(plus_nat(m, m))
                  }
  case Bit0(n) => {
                    val m: nat = nat_of_num(n);
                    plus_nat(m, m)
                  }
  case One() => one_nat
}

def gen_length[A](n: nat, x1: List[A]): nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](Suc(n), xs)
  case (n, Nil) => n
}

def name[A](x0: risk_factor_ext[A]): List[char] = x0 match {
  case risk_factor_exta(name, asset_class, risk_type, shock_type, shift, more)
    => name
}

def mapfun[A, B](fun: A => B, x1: List[A]): List[B] = (fun, x1) match {
  case (fun, Nil) => Nil
  case (fun, x :: xs) => fun(x) :: mapfun[A, B](fun, xs)
}

def names_of(l: List[risk_factor_ext[Unit]]): List[List[char]] =
  mapfun[risk_factor_ext[Unit],
          List[char]](((a: risk_factor_ext[Unit]) => name[Unit](a)), l)

def shift[A](x0: risk_factor_ext[A]): real = x0 match {
  case risk_factor_exta(name, asset_class, risk_type, shock_type, shift, more)
    => shift
}

def power[A : power](a: A, x1: nat): A = (a, x1) match {
  case (a, zero_nat()) => one[A]
  case (a, Suc(n)) => times[A](a, power[A](a, n))
}

def risk_factors: List[risk_factor_ext[Unit]] =
  List(risk_factor_exta[Unit](List(Char(true, false, true, false, false, false,
 true, false),
                                    Char(true, false, true, false, true, false,
  true, false),
                                    Char(false, true, false, false, true, false,
  true, false),
                                    Char(true, true, true, true, true, false,
  true, false),
                                    Char(true, true, true, true, false, false,
  true, false),
                                    Char(true, false, false, true, false, false,
  true, false),
                                    Char(true, true, false, false, true, false,
  true, false),
                                    Char(true, true, true, true, true, false,
  true, false),
                                    Char(false, true, false, false, true, true,
  false, false),
                                    Char(true, false, false, true, true, false,
  true, false)),
                               List(Char(true, false, false, true, false, false,
  true, false),
                                     Char(false, true, false, false, true,
   false, true, false)),
                               List(Char(true, true, false, false, true, false,
  true, false),
                                     Char(true, false, true, false, false,
   false, true, false),
                                     Char(false, true, true, true, false, false,
   true, false),
                                     Char(true, true, false, false, true, false,
   true, false),
                                     Char(true, false, false, true, false,
   false, true, false),
                                     Char(false, false, true, false, true,
   false, true, false),
                                     Char(true, false, false, true, false,
   false, true, false),
                                     Char(false, true, true, false, true, false,
   true, false),
                                     Char(true, false, false, true, false,
   false, true, false),
                                     Char(false, false, true, false, true,
   false, true, false),
                                     Char(true, false, false, true, true, false,
   true, false)),
                               List(Char(true, false, false, false, false,
  false, true, false),
                                     Char(false, true, false, false, false,
   false, true, false)),
                               divide_reala(zero_reala,
     Ratreal(of_int(int_of_integer(BigInt(10))))),
                               ()),
        risk_factor_exta[Unit](List(Char(true, false, true, false, false, false,
  true, false),
                                     Char(true, false, true, false, true, false,
   true, false),
                                     Char(false, true, false, false, true,
   false, true, false),
                                     Char(true, true, true, true, true, false,
   true, false),
                                     Char(true, true, true, true, false, false,
   true, false),
                                     Char(true, false, false, true, false,
   false, true, false),
                                     Char(true, true, false, false, true, false,
   true, false),
                                     Char(true, true, true, true, true, false,
   true, false),
                                     Char(true, false, true, false, true, true,
   false, false),
                                     Char(true, false, false, true, true, false,
   true, false)),
                                List(Char(true, false, false, true, false,
   false, true, false),
                                      Char(false, true, false, false, true,
    false, true, false)),
                                List(Char(true, true, false, false, true, false,
   true, false),
                                      Char(true, false, true, false, false,
    false, true, false),
                                      Char(false, true, true, true, false,
    false, true, false),
                                      Char(true, true, false, false, true,
    false, true, false),
                                      Char(true, false, false, true, false,
    false, true, false),
                                      Char(false, false, true, false, true,
    false, true, false),
                                      Char(true, false, false, true, false,
    false, true, false),
                                      Char(false, true, true, false, true,
    false, true, false),
                                      Char(true, false, false, true, false,
    false, true, false),
                                      Char(false, false, true, false, true,
    false, true, false),
                                      Char(true, false, false, true, true,
    false, true, false)),
                                List(Char(true, false, false, false, false,
   false, true, false),
                                      Char(false, true, false, false, false,
    false, true, false)),
                                divide_reala(zero_reala,
      Ratreal(of_int(int_of_integer(BigInt(10))))),
                                ()),
        risk_factor_exta[Unit](List(Char(true, false, true, false, true, false,
  true, false),
                                     Char(true, true, false, false, true, false,
   true, false),
                                     Char(false, false, true, false, false,
   false, true, false),
                                     Char(true, true, true, true, true, false,
   true, false),
                                     Char(true, false, false, true, false,
   false, true, false),
                                     Char(false, true, false, false, true,
   false, true, false),
                                     Char(true, true, false, false, true, false,
   true, false),
                                     Char(false, false, true, true, false,
   false, true, false),
                                     Char(true, true, false, false, true, true,
   false, false),
                                     Char(true, false, true, true, false, false,
   true, false),
                                     Char(true, true, true, true, true, false,
   true, false),
                                     Char(false, true, false, false, true, true,
   false, false),
                                     Char(true, false, false, true, true, false,
   true, false)),
                                List(Char(true, false, false, true, false,
   false, true, false),
                                      Char(false, true, false, false, true,
    false, true, false)),
                                List(Char(true, true, false, false, true, false,
   true, false),
                                      Char(true, false, true, false, false,
    false, true, false),
                                      Char(false, true, true, true, false,
    false, true, false),
                                      Char(true, true, false, false, true,
    false, true, false),
                                      Char(true, false, false, true, false,
    false, true, false),
                                      Char(false, false, true, false, true,
    false, true, false),
                                      Char(true, false, false, true, false,
    false, true, false),
                                      Char(false, true, true, false, true,
    false, true, false),
                                      Char(true, false, false, true, false,
    false, true, false),
                                      Char(false, false, true, false, true,
    false, true, false),
                                      Char(true, false, false, true, true,
    false, true, false)),
                                List(Char(false, true, false, false, true,
   false, true, false),
                                      Char(true, false, true, false, false,
    false, true, false)),
                                divide_reala(Ratreal(of_int(int_of_integer(BigInt(4)))),
      power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                   nat_of_num(Bit0(One())))),
                                ()),
        risk_factor_exta[Unit](List(Char(true, false, false, true, false, false,
  true, false),
                                     Char(false, true, false, false, false,
   false, true, false),
                                     Char(true, false, true, true, false, false,
   true, false)),
                                List(Char(true, true, false, false, false,
   false, true, false),
                                      Char(false, true, false, false, true,
    false, true, false)),
                                List(Char(true, true, false, false, true, false,
   true, false),
                                      Char(true, false, true, false, false,
    false, true, false),
                                      Char(false, true, true, true, false,
    false, true, false),
                                      Char(true, true, false, false, true,
    false, true, false),
                                      Char(true, false, false, true, false,
    false, true, false),
                                      Char(false, false, true, false, true,
    false, true, false),
                                      Char(true, false, false, true, false,
    false, true, false),
                                      Char(false, true, true, false, true,
    false, true, false),
                                      Char(true, false, false, true, false,
    false, true, false),
                                      Char(false, false, true, false, true,
    false, true, false),
                                      Char(true, false, false, true, true,
    false, true, false)),
                                List(Char(true, false, false, false, false,
   false, true, false),
                                      Char(false, true, false, false, false,
    false, true, false)),
                                divide_reala(zero_reala,
      Ratreal(of_int(int_of_integer(BigInt(10))))),
                                ()),
        risk_factor_exta[Unit](List(Char(true, true, false, false, true, false,
  true, false),
                                     Char(false, false, false, false, true,
   false, true, false),
                                     Char(true, false, true, false, true, true,
   false, false),
                                     Char(false, false, false, false, true,
   true, false, false),
                                     Char(false, false, false, false, true,
   true, false, false)),
                                List(Char(true, false, true, false, false,
   false, true, false),
                                      Char(true, false, false, false, true,
    false, true, false)),
                                List(Char(true, false, true, false, false,
   false, true, false),
                                      Char(false, false, false, true, true,
    false, true, false),
                                      Char(false, false, false, false, true,
    false, true, false),
                                      Char(true, true, true, true, false, false,
    true, false),
                                      Char(true, true, false, false, true,
    false, true, false),
                                      Char(true, false, true, false, true,
    false, true, false),
                                      Char(false, true, false, false, true,
    false, true, false),
                                      Char(true, false, true, false, false,
    false, true, false)),
                                List(Char(false, true, false, false, true,
   false, true, false),
                                      Char(true, false, true, false, false,
    false, true, false)),
                                divide_reala(zero_reala,
      Ratreal(of_int(int_of_integer(BigInt(10))))),
                                ()),
        risk_factor_exta[Unit](List(Char(false, false, false, true, true, false,
  true, false),
                                     Char(true, false, false, false, false,
   false, true, false),
                                     Char(true, false, true, false, true, false,
   true, false)),
                                List(Char(true, true, false, false, false,
   false, true, false),
                                      Char(true, true, true, true, false, false,
    true, false)),
                                List(Char(true, false, true, false, false,
   false, true, false),
                                      Char(false, false, false, true, true,
    false, true, false),
                                      Char(false, false, false, false, true,
    false, true, false),
                                      Char(true, true, true, true, false, false,
    true, false),
                                      Char(true, true, false, false, true,
    false, true, false),
                                      Char(true, false, true, false, true,
    false, true, false),
                                      Char(false, true, false, false, true,
    false, true, false),
                                      Char(true, false, true, false, false,
    false, true, false)),
                                List(Char(false, true, false, false, true,
   false, true, false),
                                      Char(true, false, true, false, false,
    false, true, false)),
                                divide_reala(zero_reala,
      Ratreal(of_int(int_of_integer(BigInt(10))))),
                                ()))

def filter[A, B : equal](x0: List[A], compare: B, selector: A => B): List[A] =
  (x0, compare, selector) match {
  case (Nil, compare, selector) => Nil
  case (x :: xs, compare, selector) =>
    (if (eq[B](selector(x), compare)) x :: filter[A, B](xs, compare, selector)
      else filter[A, B](xs, compare, selector))
}

def lookup[A, B : equal](list: List[A], compare: B, selector: A => B): A =
  nth[A](filter[A, B](list, compare, selector), zero_nat())

def get_shift(asset_name: List[char]): real =
  (if (nulla[risk_factor_ext[Unit]](filter[risk_factor_ext[Unit],
    List[char]](risk_factors, asset_name,
                 ((a: risk_factor_ext[Unit]) => name[Unit](a)))))
    zero_reala
    else shift[Unit](lookup[risk_factor_ext[Unit],
                             List[char]](risk_factors, asset_name,
  ((a: risk_factor_ext[Unit]) => name[Unit](a)))))

def asset_class[A](x0: risk_factor_ext[A]): List[char] = x0 match {
  case risk_factor_exta(name, asset_class, risk_type, shock_type, shift, more)
    => asset_class
}

def accumulate_holding_names_aux(str: List[char]): List[List[char]] =
  {
    val a: List[risk_factor_ext[Unit]] =
      filter[risk_factor_ext[Unit],
              List[char]](risk_factors, str,
                           ((a: risk_factor_ext[Unit]) =>
                             asset_class[Unit](a)));
    names_of(a)
  }

def currencies: List[List[char]] =
  List(List(Char(true, false, true, false, false, false, true, false),
             Char(true, false, true, false, true, false, true, false),
             Char(false, true, false, false, true, false, true, false)),
        List(Char(true, false, true, false, true, false, true, false),
              Char(true, true, false, false, true, false, true, false),
              Char(false, false, true, false, false, false, true, false)),
        List(Char(true, true, true, false, false, false, true, false),
              Char(false, true, false, false, false, false, true, false),
              Char(false, false, false, false, true, false, true, false)))

def accumulate_holding_names(str: List[char]): List[List[char]] =
  (if (equal_lista[char](str, List(Char(true, false, false, true, false, false,
 true, false),
                                    Char(false, true, false, false, true, false,
  true, false))))
    currencies ++ accumulate_holding_names_aux(str)
    else accumulate_holding_names_aux(str))

def size_list[A]: (List[A]) => nat =
  ((a: List[A]) => gen_length[A](zero_nat(), a))

def insort_key[A, B : linorder](f: A => B, x: A, xa2: List[A]): List[A] =
  (f, x, xa2) match {
  case (f, x, Nil) => List(x)
  case (f, x, y :: ys) =>
    (if (less_eq[B](f(x), f(y))) x :: y :: ys
      else y :: insort_key[A, B](f, x, ys))
}

def sort_key[A, B : linorder](f: A => B, xs: List[A]): List[A] =
  (foldr[A, List[A]](((a: A) => (b: List[A]) => insort_key[A, B](f, a, b)),
                      xs)).apply(Nil)

def of_nat_aux[A : semiring_1](inc: A => A, x1: nat, i: A): A = (inc, x1, i)
  match {
  case (inc, zero_nat(), i) => i
  case (inc, Suc(n), i) => of_nat_aux[A](inc, n, inc(i))
}

def of_nat[A : semiring_1](n: nat): A =
  of_nat_aux[A](((i: A) => plus[A](i, one[A])), n, zero[A])

def ceiling[A : floor_ceiling](x: A): int = uminus_int(floor[A](uminus[A](x)))

def percentile_impl(values: List[real], level: real): real =
  {
    val size: real = of_nat[real](size_list[real].apply(values))
    val sorted: List[real] = sort_key[real, real](((x: real) => x), values)
    val i: int =
      ceiling[real](minus_reala(times_reala(size, level),
                                 divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
       Ratreal(of_int(int_of_integer(BigInt(10)))))))
    val lower: real =
      divide_reala(minus_reala(Ratreal(of_int(i)),
                                divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
      Ratreal(of_int(int_of_integer(BigInt(10)))))),
                    size)
    val upper: real =
      divide_reala(plus_reala(Ratreal(of_int(i)),
                               divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
     Ratreal(of_int(int_of_integer(BigInt(10)))))),
                    size)
    val lower_value: real = nth[real](sorted, nat.apply(minus_int(i, one_int)))
    val upper_value: real = nth[real](sorted, nat.apply(i));
    plus_reala(lower_value,
                divide_reala(times_reala(minus_reala(level, lower),
  minus_reala(upper_value, lower_value)),
                              minus_reala(upper, lower)))
  }

def get_currency_number(x: List[char]): nat =
  (if (equal_lista[char](x, List(Char(true, false, true, false, false, false,
                                       true, false),
                                  Char(true, false, true, false, true, false,
true, false),
                                  Char(false, true, false, false, true, false,
true, false))))
    zero_nat()
    else (if (equal_lista[char](x, List(Char(true, false, true, false, true,
      false, true, false),
 Char(true, true, false, false, true, false, true, false),
 Char(false, false, true, false, false, false, true, false))))
           one_nat else nat_of_num(Bit0(One()))))

def risk_type[A](x0: risk_factor_ext[A]): List[char] = x0 match {
  case risk_factor_exta(name, asset_class, risk_type, shock_type, shift, more)
    => risk_type
}

def get_sensitivity(asset_name: List[char]): Boolean =
  (if (nulla[risk_factor_ext[Unit]](filter[risk_factor_ext[Unit],
    List[char]](risk_factors, asset_name,
                 ((a: risk_factor_ext[Unit]) => name[Unit](a)))) ||
         equal_lista[char](risk_type[Unit](lookup[risk_factor_ext[Unit],
           List[char]](risk_factors, asset_name,
                        ((a: risk_factor_ext[Unit]) => name[Unit](a)))),
                            List(Char(true, true, false, false, true, false,
                                       true, false),
                                  Char(true, false, true, false, false, false,
true, false),
                                  Char(false, true, true, true, false, false,
true, false),
                                  Char(true, true, false, false, true, false,
true, false),
                                  Char(true, false, false, true, false, false,
true, false),
                                  Char(false, false, true, false, true, false,
true, false),
                                  Char(true, false, false, true, false, false,
true, false),
                                  Char(false, true, true, false, true, false,
true, false),
                                  Char(true, false, false, true, false, false,
true, false),
                                  Char(false, false, true, false, true, false,
true, false),
                                  Char(true, false, false, true, true, false,
true, false))))
    true else false)

def base_level[A](x0: risk_factor_base_level_ext[A]): real = x0 match {
  case risk_factor_base_level_exta(name, base_level, more) => base_level
}

def named[A](x0: risk_factor_base_level_ext[A]): List[char] = x0 match {
  case risk_factor_base_level_exta(name, base_level, more) => name
}

def risk_factor_base_levels: List[risk_factor_base_level_ext[Unit]] =
  List(risk_factor_base_level_exta[Unit](List(Char(true, false, true, false,
            false, false, true, false),
       Char(true, false, true, false, true, false, true, false),
       Char(false, true, false, false, true, false, true, false),
       Char(true, true, true, true, true, false, true, false),
       Char(true, true, true, true, false, false, true, false),
       Char(true, false, false, true, false, false, true, false),
       Char(true, true, false, false, true, false, true, false),
       Char(true, true, true, true, true, false, true, false),
       Char(false, true, false, false, true, true, false, false),
       Char(true, false, false, true, true, false, true, false)),
  uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
  nat_of_num(Bit0(Bit0(One())))))),
  ()),
        risk_factor_base_level_exta[Unit](List(Char(true, false, true, false,
             false, false, true, false),
        Char(true, false, true, false, true, false, true, false),
        Char(false, true, false, false, true, false, true, false),
        Char(true, true, true, true, true, false, true, false),
        Char(true, true, true, true, false, false, true, false),
        Char(true, false, false, true, false, false, true, false),
        Char(true, true, false, false, true, false, true, false),
        Char(true, true, true, true, true, false, true, false),
        Char(true, false, true, false, true, true, false, false),
        Char(true, false, false, true, true, false, true, false)),
   divide_reala(Ratreal(of_int(int_of_integer(BigInt(25)))),
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit0(Bit0(One()))))),
   ()),
        risk_factor_base_level_exta[Unit](List(Char(true, false, true, false,
             true, false, true, false),
        Char(true, true, false, false, true, false, true, false),
        Char(false, false, true, false, false, false, true, false),
        Char(true, true, true, true, true, false, true, false),
        Char(true, false, false, true, false, false, true, false),
        Char(false, true, false, false, true, false, true, false),
        Char(true, true, false, false, true, false, true, false),
        Char(false, false, true, true, false, false, true, false),
        Char(true, true, false, false, true, true, false, false),
        Char(true, false, true, true, false, false, true, false),
        Char(true, true, true, true, true, false, true, false),
        Char(false, true, false, false, true, true, false, false),
        Char(true, false, false, true, true, false, true, false)),
   divide_reala(one_reala,
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit0(One())))),
   ()),
        risk_factor_base_level_exta[Unit](List(Char(true, false, false, true,
             false, false, true, false),
        Char(false, true, false, false, false, false, true, false),
        Char(true, false, true, true, false, false, true, false)),
   divide_reala(Ratreal(of_int(int_of_integer(BigInt(12)))),
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit1(One())))),
   ()),
        risk_factor_base_level_exta[Unit](List(Char(true, true, false, false,
             true, false, true, false),
        Char(false, false, false, false, true, false, true, false),
        Char(true, false, true, false, true, true, false, false),
        Char(false, false, false, false, true, true, false, false),
        Char(false, false, false, false, true, true, false, false)),
   Ratreal(of_int(int_of_integer(BigInt(1000)))), ()),
        risk_factor_base_level_exta[Unit](List(Char(false, false, false, true,
             true, false, true, false),
        Char(true, false, false, false, false, false, true, false),
        Char(true, false, true, false, true, false, true, false)),
   Ratreal(of_int(int_of_integer(BigInt(1200)))), ()))

def get_base_level(asset_name: List[char]): real =
  (if (nulla[risk_factor_base_level_ext[Unit]](filter[risk_factor_base_level_ext[Unit],
               List[char]](risk_factor_base_levels, asset_name,
                            ((a: risk_factor_base_level_ext[Unit]) =>
                              named[Unit](a)))))
    zero_reala
    else base_level[Unit](lookup[risk_factor_base_level_ext[Unit],
                                  List[char]](risk_factor_base_levels,
       asset_name, ((a: risk_factor_base_level_ext[Unit]) => named[Unit](a)))))

def fx_matrix: List[List[real]] =
  List(List(one_reala,
             divide_reala(Ratreal(of_int(int_of_integer(BigInt(7)))),
                           Ratreal(of_int(int_of_integer(BigInt(5))))),
             divide_reala(Ratreal(of_int(int_of_integer(BigInt(7)))),
                           Ratreal(of_int(int_of_integer(BigInt(8)))))),
        List(divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                           Ratreal(of_int(int_of_integer(BigInt(7))))),
              one_reala,
              divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                            Ratreal(of_int(int_of_integer(BigInt(8)))))),
        List(divide_reala(Ratreal(of_int(int_of_integer(BigInt(8)))),
                           Ratreal(of_int(int_of_integer(BigInt(7))))),
              divide_reala(Ratreal(of_int(int_of_integer(BigInt(8)))),
                            Ratreal(of_int(int_of_integer(BigInt(5))))),
              one_reala))

def amount_in_euro(value_in_curr: real, xcurr: nat): real =
  times_reala(value_in_curr,
               nth[real](nth[List[real]](fx_matrix, xcurr), zero_nat()))

def shock_type[A](x0: risk_factor_ext[A]): List[char] = x0 match {
  case risk_factor_exta(name, asset_class, risk_type, shock_type, shift, more)
    => shock_type
}

def get_relative(asset_name: List[char]): Boolean =
  (if (nulla[risk_factor_ext[Unit]](filter[risk_factor_ext[Unit],
    List[char]](risk_factors, asset_name,
                 ((a: risk_factor_ext[Unit]) => name[Unit](a)))))
    false
    else {
           val shock_typea: List[char] =
             shock_type[Unit](lookup[risk_factor_ext[Unit],
                                      List[char]](risk_factors, asset_name,
           ((a: risk_factor_ext[Unit]) => name[Unit](a))));
           (if (equal_lista[char](shock_typea,
                                   List(Char(false, true, false, false, true,
      false, true, false),
 Char(true, false, true, false, false, false, true, false))))
             true else false)
         })

def currency[A](x0: portfolio_derivative_ext[A]): nat = x0 match {
  case portfolio_derivative_exta(name, amount, currency, more) => currency
}

def namec[A](x0: portfolio_derivative_ext[A]): List[char] = x0 match {
  case portfolio_derivative_exta(name, amount, currency, more) => name
}

def USD: nat = one_nat

def GBP: nat = nat_of_num(Bit0(One()))

def EUR: nat = zero_nat()

def portfolio_derivatives: List[portfolio_derivative_ext[Unit]] =
  List(portfolio_derivative_exta[Unit](List(Char(true, false, true, false,
          false, false, true, false),
     Char(true, false, true, false, true, false, true, false),
     Char(false, true, false, false, true, false, true, false),
     Char(true, true, true, true, true, false, true, false),
     Char(true, true, true, true, false, false, true, false),
     Char(true, false, false, true, false, false, true, false),
     Char(true, true, false, false, true, false, true, false),
     Char(true, true, true, true, true, false, true, false),
     Char(false, true, false, false, true, true, false, false),
     Char(true, false, false, true, true, false, true, false)),
int_of_integer(BigInt(100000)), EUR, ()),
        portfolio_derivative_exta[Unit](List(Char(true, false, true, false,
           false, false, true, false),
      Char(true, false, true, false, true, false, true, false),
      Char(false, true, false, false, true, false, true, false),
      Char(true, true, true, true, true, false, true, false),
      Char(true, true, true, true, false, false, true, false),
      Char(true, false, false, true, false, false, true, false),
      Char(true, true, false, false, true, false, true, false),
      Char(true, true, true, true, true, false, true, false),
      Char(true, false, true, false, true, true, false, false),
      Char(true, false, false, true, true, false, true, false)),
 uminus_int(int_of_integer(BigInt(20000))), EUR, ()),
        portfolio_derivative_exta[Unit](List(Char(true, false, true, false,
           true, false, true, false),
      Char(true, true, false, false, true, false, true, false),
      Char(false, false, true, false, false, false, true, false),
      Char(true, true, true, true, true, false, true, false),
      Char(true, false, false, true, false, false, true, false),
      Char(false, true, false, false, true, false, true, false),
      Char(true, true, false, false, true, false, true, false),
      Char(false, false, true, true, false, false, true, false),
      Char(true, true, false, false, true, true, false, false),
      Char(true, false, true, true, false, false, true, false),
      Char(true, true, true, true, true, false, true, false),
      Char(false, true, false, false, true, true, false, false),
      Char(true, false, false, true, true, false, true, false)),
 int_of_integer(BigInt(20000)), EUR, ()),
        portfolio_derivative_exta[Unit](List(Char(true, false, false, true,
           false, false, true, false),
      Char(false, true, false, false, false, false, true, false),
      Char(true, false, true, true, false, false, true, false)),
 int_of_integer(BigInt(30300)), EUR, ()),
        portfolio_derivative_exta[Unit](List(Char(true, true, false, false,
           true, false, true, false),
      Char(false, false, false, false, true, false, true, false),
      Char(true, false, true, false, true, true, false, false),
      Char(false, false, false, false, true, true, false, false),
      Char(false, false, false, false, true, true, false, false)),
 int_of_integer(BigInt(100000)), USD, ()),
        portfolio_derivative_exta[Unit](List(Char(false, false, false, true,
           true, false, true, false),
      Char(true, false, false, false, false, false, true, false),
      Char(true, false, true, false, true, false, true, false)),
 uminus_int(int_of_integer(BigInt(123456))), USD, ()),
        portfolio_derivative_exta[Unit](List(Char(true, false, true, false,
           false, false, true, false),
      Char(true, false, true, false, true, false, true, false),
      Char(false, true, false, false, true, false, true, false)),
 int_of_integer(BigInt(1000000)), EUR, ()),
        portfolio_derivative_exta[Unit](List(Char(true, false, true, false,
           true, false, true, false),
      Char(true, true, false, false, true, false, true, false),
      Char(false, false, true, false, false, false, true, false)),
 uminus_int(int_of_integer(BigInt(1400000))), GBP, ()),
        portfolio_derivative_exta[Unit](List(Char(true, true, true, false,
           false, false, true, false),
      Char(false, true, false, false, false, false, true, false),
      Char(false, false, false, false, true, false, true, false)),
 int_of_integer(BigInt(200000)), USD, ()))

def get_currency(asset_name: List[char]): nat =
  currency[Unit](lookup[portfolio_derivative_ext[Unit],
                         List[char]](portfolio_derivatives, asset_name,
                                      ((a: portfolio_derivative_ext[Unit]) =>
namec[Unit](a))))

def compute_market_level(shock: real, local_base_level: real, shift_value: real,
                          is_relative: Boolean, is_sensitivity: Boolean):
      real
  =
  (if (is_relative)
    (if (is_sensitivity)
      times_reala(minus_reala(shock, one_reala),
                   plus_reala(local_base_level, shift_value))
      else times_reala(shock, local_base_level))
    else (if (is_sensitivity) shock
           else times_reala(shock, plus_reala(local_base_level, shift_value))))

def profit_loss(x_shock: real, x_is_sensitivity: Boolean, x_amount: real,
                 x_curr: nat, x_base_level: real, x_shift_value: real,
                 x_is_relative: Boolean):
      real
  =
  (if (x_is_sensitivity)
    amount_in_euro(times_reala(x_amount,
                                compute_market_level(x_shock, x_base_level,
              x_shift_value, x_is_relative, x_is_sensitivity)),
                    x_curr)
    else amount_in_euro(times_reala(x_amount,
                                     divide_reala(minus_reala(compute_market_level(x_shock,
    x_base_level, x_shift_value, x_is_relative, x_is_sensitivity),
                       x_base_level),
           x_base_level)),
                         x_curr))

def shocksa[A](x0: risk_factor_shock_ext[A]): List[real] = x0 match {
  case risk_factor_shock_exta(name, shocks, more) => shocks
}

def nameb[A](x0: risk_factor_shock_ext[A]): List[char] = x0 match {
  case risk_factor_shock_exta(name, shocks, more) => name
}

def shocks[A](x0: fx_rate_shock_ext[A]): List[real] = x0 match {
  case fx_rate_shock_exta(name, currency, shocks, more) => shocks
}

def risk_factor_shocks: List[risk_factor_shock_ext[Unit]] =
  List(risk_factor_shock_exta[Unit](List(Char(true, false, true, false, false,
       false, true, false),
  Char(true, false, true, false, true, false, true, false),
  Char(false, true, false, false, true, false, true, false),
  Char(true, true, true, true, true, false, true, false),
  Char(true, true, true, true, false, false, true, false),
  Char(true, false, false, true, false, false, true, false),
  Char(true, true, false, false, true, false, true, false),
  Char(true, true, true, true, true, false, true, false),
  Char(false, true, false, false, true, true, false, false),
  Char(true, false, false, true, true, false, true, false)),
                                     List(divide_reala(one_reala,
                power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                             nat_of_num(Bit0(Bit0(One()))))),
   uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
   nat_of_num(Bit0(Bit0(One())))))),
   uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
   nat_of_num(Bit1(One()))))),
   zero_reala,
   divide_reala(Ratreal(of_int(int_of_integer(BigInt(2)))),
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit0(Bit0(One()))))),
   divide_reala(one_reala,
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit0(Bit0(One()))))),
   uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
   nat_of_num(Bit0(Bit0(One())))))),
   uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
   nat_of_num(Bit1(One()))))),
   divide_reala(one_reala,
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit0(Bit0(One()))))),
   uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
   nat_of_num(Bit0(Bit0(One())))))),
   uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
   nat_of_num(Bit1(One()))))),
   zero_reala, zero_reala,
   divide_reala(Ratreal(of_int(int_of_integer(BigInt(2)))),
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit0(Bit0(One()))))),
   divide_reala(one_reala,
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit0(Bit0(One()))))),
   uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
   nat_of_num(Bit0(Bit0(One())))))),
   uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
   nat_of_num(Bit1(One()))))),
   zero_reala,
   divide_reala(Ratreal(of_int(int_of_integer(BigInt(2)))),
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit0(Bit0(One()))))),
   divide_reala(Ratreal(of_int(int_of_integer(BigInt(2)))),
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit0(Bit0(One()))))),
   divide_reala(one_reala,
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit0(Bit0(One()))))),
   uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
   nat_of_num(Bit0(Bit0(One())))))),
   uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
   nat_of_num(Bit1(One()))))),
   zero_reala,
   divide_reala(Ratreal(of_int(int_of_integer(BigInt(2)))),
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit0(Bit0(One())))))),
                                     ()),
        risk_factor_shock_exta[Unit](List(Char(true, false, true, false, false,
        false, true, false),
   Char(true, false, true, false, true, false, true, false),
   Char(false, true, false, false, true, false, true, false),
   Char(true, true, true, true, true, false, true, false),
   Char(true, true, true, true, false, false, true, false),
   Char(true, false, false, true, false, false, true, false),
   Char(true, true, false, false, true, false, true, false),
   Char(true, true, true, true, true, false, true, false),
   Char(true, false, true, false, true, true, false, false),
   Char(true, false, false, true, true, false, true, false)),
                                      List(zero_reala, zero_reala, zero_reala,
    zero_reala, zero_reala, zero_reala, zero_reala, zero_reala, zero_reala,
    zero_reala, zero_reala, zero_reala, zero_reala, zero_reala, zero_reala,
    zero_reala, zero_reala, zero_reala, zero_reala, zero_reala, zero_reala,
    zero_reala, zero_reala, zero_reala, zero_reala),
                                      ()),
        risk_factor_shock_exta[Unit](List(Char(true, false, true, false, true,
        false, true, false),
   Char(true, true, false, false, true, false, true, false),
   Char(false, false, true, false, false, false, true, false),
   Char(true, true, true, true, true, false, true, false),
   Char(true, false, false, true, false, false, true, false),
   Char(false, true, false, false, true, false, true, false),
   Char(true, true, false, false, true, false, true, false),
   Char(false, false, true, true, false, false, true, false),
   Char(true, true, false, false, true, true, false, false),
   Char(true, false, true, true, false, false, true, false),
   Char(true, true, true, true, true, false, true, false),
   Char(false, true, false, false, true, true, false, false),
   Char(true, false, false, true, true, false, true, false)),
                                      List(divide_reala(Ratreal(of_int(int_of_integer(BigInt(10025)))),
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(10025)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(9975)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(9975)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    one_reala, one_reala,
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(10025)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(9975)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    one_reala, one_reala, one_reala, one_reala, one_reala, one_reala,
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(10025)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(9975)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    one_reala, one_reala, one_reala, one_reala,
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(10025)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(9975)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    one_reala, one_reala, one_reala),
                                      ()),
        risk_factor_shock_exta[Unit](List(Char(true, false, false, true, false,
        false, true, false),
   Char(false, true, false, false, false, false, true, false),
   Char(true, false, true, true, false, false, true, false)),
                                      List(divide_reala(one_reala,
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit0(Bit0(One()))))),
    uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                               power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
    nat_of_num(Bit0(Bit0(One())))))),
    uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(5)))),
                               power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
    nat_of_num(Bit1(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(2)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(6)))),
                               power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
    nat_of_num(Bit0(Bit0(One())))))),
    uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(51)))),
                               power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
    nat_of_num(Bit0(Bit0(One())))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(3)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(7)))),
                               power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
    nat_of_num(Bit0(Bit0(One())))))),
    uminus_reala(divide_reala(Ratreal(of_int(int_of_integer(BigInt(52)))),
                               power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
    nat_of_num(Bit0(Bit0(One())))))),
    zero_reala,
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(4)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    uminus_reala(divide_reala(one_reala,
                               power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
    nat_of_num(Bit0(Bit0(One())))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(11)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(8)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(12)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One())))))),
                                      ()),
        risk_factor_shock_exta[Unit](List(Char(true, true, false, false, true,
        false, true, false),
   Char(false, false, false, false, true, false, true, false),
   Char(true, false, true, false, true, true, false, false),
   Char(false, false, false, false, true, true, false, false),
   Char(false, false, false, false, true, true, false, false)),
                                      List(divide_reala(Ratreal(of_int(int_of_integer(BigInt(1011)))),
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit1(One())))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(995)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit1(One())))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(997)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit1(One())))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(1001)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit1(One())))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(10002)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(101)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(One())))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(9955)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(9975)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(10012)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(10003)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(10101)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(9951)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One())))))),
                                      ()),
        risk_factor_shock_exta[Unit](List(Char(false, false, false, true, true,
        false, true, false),
   Char(true, false, false, false, false, false, true, false),
   Char(true, false, true, false, true, false, true, false)),
                                      List(divide_reala(Ratreal(of_int(int_of_integer(BigInt(101)))),
                 power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                              nat_of_num(Bit0(One())))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(995)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit1(One())))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(997)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit1(One())))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(1001)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit1(One())))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(9955)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(10002)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(1011)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit1(One())))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(994)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit1(One())))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(9975)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(1003)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit1(One())))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(99)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(One())))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(10004)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One()))))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(1012)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit1(One())))),
    divide_reala(Ratreal(of_int(int_of_integer(BigInt(9945)))),
                  power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                               nat_of_num(Bit0(Bit0(One())))))),
                                      ()))

def namea[A](x0: fx_rate_shock_ext[A]): List[char] = x0 match {
  case fx_rate_shock_exta(name, currency, shocks, more) => name
}

def fx_rate_shocks_source: List[fx_rate_shock_ext[Unit]] =
  List(fx_rate_shock_exta[Unit](List(Char(true, false, true, false, true, false,
   true, false),
                                      Char(true, true, false, false, true,
    false, true, false),
                                      Char(false, false, true, false, false,
    false, true, false)),
                                 EUR,
                                 List(one_reala,
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(1001)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit1(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(9975)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit0(Bit0(One()))))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(995)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit1(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(10002)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit0(Bit0(One()))))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(101)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit0(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(995)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit1(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(997)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit1(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(1001)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit1(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(10002)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit0(Bit0(One()))))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(101)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit0(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(995)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit1(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(997)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit1(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(1001)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit1(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(10002)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit0(Bit0(One()))))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(101)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit0(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(995)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit1(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(997)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit1(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(1001)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit1(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(10002)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit0(Bit0(One()))))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(101)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit0(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(995)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit1(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(997)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit1(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(1001)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit1(One())))),
                                       divide_reala(Ratreal(of_int(int_of_integer(BigInt(10002)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit0(Bit0(One())))))),
                                 ()),
        fx_rate_shock_exta[Unit](List(Char(true, true, true, false, false,
    false, true, false),
                                       Char(false, true, false, false, false,
     false, true, false),
                                       Char(false, false, false, false, true,
     false, true, false)),
                                  USD,
                                  List(divide_reala(Ratreal(of_int(int_of_integer(BigInt(9985)))),
             power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                          nat_of_num(Bit0(Bit0(One()))))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(1002)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit1(One())))),
one_reala,
divide_reala(Ratreal(of_int(int_of_integer(BigInt(995)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit1(One())))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(10003)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit0(Bit0(One()))))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(101)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit0(One())))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(994)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit1(One())))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(996)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit1(One())))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(1001)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit1(One())))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(10002)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit0(Bit0(One()))))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(101)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit0(One())))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(1005)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit1(One())))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(9999)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit0(Bit0(One()))))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(9999)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit0(Bit0(One()))))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(10011)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit0(Bit0(One()))))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(1005)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit1(One())))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(996)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit1(One())))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(998)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit1(One())))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(10025)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit0(Bit0(One()))))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(101)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit0(One())))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(995)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit1(One())))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(997)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit1(One())))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(1001)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit1(One())))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(10002)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit0(Bit0(One()))))),
divide_reala(Ratreal(of_int(int_of_integer(BigInt(10001)))),
              power[real](Ratreal(of_int(int_of_integer(BigInt(10)))),
                           nat_of_num(Bit0(Bit0(One())))))),
                                  ()))

def USD_shocks_in_euros: List[real] =
  mapfun[real,
          real](((usd: real) =>
                  times_reala(minus_reala(usd, one_reala),
                               nth[real](nth[List[real]](fx_matrix, zero_nat()),
  get_currency_number(List(Char(true, false, true, false, true, false, true,
                                 false),
                            Char(true, true, false, false, true, false, true,
                                  false),
                            Char(false, false, true, false, false, false, true,
                                  false)))))),
                 shocks[Unit](lookup[fx_rate_shock_ext[Unit],
                                      List[char]](fx_rate_shocks_source,
           List(Char(true, false, true, false, true, false, true, false),
                 Char(true, true, false, false, true, false, true, false),
                 Char(false, false, true, false, false, false, true, false)),
           ((a: fx_rate_shock_ext[Unit]) => namea[Unit](a)))))

def mapfun2[A, B, C](fun: A => B => C, x1: List[A], x2: List[B]): List[C] =
  (fun, x1, x2) match {
  case (fun, Nil, Nil) => Nil
  case (fun, x :: xs, y :: ys) => (fun(x))(y) :: mapfun2[A, B, C](fun, xs, ys)
  case (fun, v :: va, Nil) => sys.error("undefined")
  case (fun, Nil, v :: va) => sys.error("undefined")
}

def GBP_shocks_in_euros: List[real] =
  mapfun2[real, real,
           real](((usd: real) => (gbp: real) =>
                   times_reala(divide_reala(nth[real](nth[List[real]](fx_matrix,
                               zero_nat()),
               get_currency_number(List(Char(true, false, true, false, true,
      false, true, false),
 Char(true, true, false, false, true, false, true, false),
 Char(false, false, true, false, false, false, true, false)))),
     nth[real](nth[List[real]](fx_matrix,
                                get_currency_number(List(Char(true, true, true,
                       false, false, false, true, false),
                  Char(false, true, false, false, false, false, true, false),
                  Char(false, false, false, false, true, false, true, false)))),
                get_currency_number(List(Char(true, false, true, false, true,
       false, true, false),
  Char(true, true, false, false, true, false, true, false),
  Char(false, false, true, false, false, false, true, false))))),
                                minus_reala(divide_reala(usd, gbp),
     one_reala))),
                  shocks[Unit](lookup[fx_rate_shock_ext[Unit],
                                       List[char]](fx_rate_shocks_source,
            List(Char(true, false, true, false, true, false, true, false),
                  Char(true, true, false, false, true, false, true, false),
                  Char(false, false, true, false, false, false, true, false)),
            ((a: fx_rate_shock_ext[Unit]) => namea[Unit](a)))),
                  shocks[Unit](lookup[fx_rate_shock_ext[Unit],
                                       List[char]](fx_rate_shocks_source,
            List(Char(true, true, true, false, false, false, true, false),
                  Char(false, true, false, false, false, false, true, false),
                  Char(false, false, false, false, true, false, true, false)),
            ((a: fx_rate_shock_ext[Unit]) => namea[Unit](a)))))

def fx_rate_shocks: List[fx_rate_shock_ext[Unit]] =
  List(fx_rate_shock_exta[Unit](List(Char(true, false, true, false, true, false,
   true, false),
                                      Char(true, true, false, false, true,
    false, true, false),
                                      Char(false, false, true, false, false,
    false, true, false)),
                                 zero_nat(), USD_shocks_in_euros, ()),
        fx_rate_shock_exta[Unit](List(Char(true, true, true, false, false,
    false, true, false),
                                       Char(false, true, false, false, false,
     false, true, false),
                                       Char(false, false, false, false, true,
     false, true, false)),
                                  zero_nat(), GBP_shocks_in_euros, ()),
        fx_rate_shock_exta[Unit](List(Char(true, false, true, false, false,
    false, true, false),
                                       Char(true, false, true, false, true,
     false, true, false),
                                       Char(false, true, false, false, true,
     false, true, false)),
                                  zero_nat(),
                                  List(zero_reala, zero_reala, zero_reala,
zero_reala, zero_reala, zero_reala, zero_reala, zero_reala, zero_reala,
zero_reala, zero_reala, zero_reala, zero_reala, zero_reala, zero_reala,
zero_reala, zero_reala, zero_reala, zero_reala, zero_reala, zero_reala,
zero_reala, zero_reala, zero_reala, zero_reala),
                                  ()))

def get_shocks(asset_name: List[char]): List[real] =
  (if (member[List[char]](currencies, asset_name))
    shocks[Unit](lookup[fx_rate_shock_ext[Unit],
                         List[char]](fx_rate_shocks, asset_name,
                                      ((a: fx_rate_shock_ext[Unit]) =>
namea[Unit](a))))
    else shocksa[Unit](lookup[risk_factor_shock_ext[Unit],
                               List[char]](risk_factor_shocks, asset_name,
    ((a: risk_factor_shock_ext[Unit]) => nameb[Unit](a)))))

def amountb[A](x0: portfolio_variation_margin_ext[A]): int = x0 match {
  case portfolio_variation_margin_exta(name, amount, currency, more) => amount
}

def namef[A](x0: portfolio_variation_margin_ext[A]): List[char] = x0 match {
  case portfolio_variation_margin_exta(name, amount, currency, more) => name
}

def portfolio_variation_margins: List[portfolio_variation_margin_ext[Unit]] =
  List(portfolio_variation_margin_exta[Unit](List(Char(true, true, true, false,
                false, false, true, false),
           Char(false, true, false, false, false, false, true, false),
           Char(false, false, false, false, true, false, true, false)),
      int_of_integer(BigInt(150000)), USD, ()))

def get_amount_portfolio_variation_margin(asset_name: List[char]): real =
  Ratreal(of_int({
                   val portfolio_variation_marginsa:
                         List[portfolio_variation_margin_ext[Unit]]
                     = filter[portfolio_variation_margin_ext[Unit],
                               List[char]](portfolio_variation_margins,
    asset_name, ((a: portfolio_variation_margin_ext[Unit]) => namef[Unit](a)));
                   (if (nulla[portfolio_variation_margin_ext[Unit]](portfolio_variation_marginsa))
                     zero_int
                     else amountb[Unit](nth[portfolio_variation_margin_ext[Unit]](portfolio_variation_marginsa,
   zero_nat())))
                 }))

def amounta[A](x0: portfolio_initial_margin_ext[A]): int = x0 match {
  case portfolio_initial_margin_exta(name, amount, currency, more) => amount
}

def namee[A](x0: portfolio_initial_margin_ext[A]): List[char] = x0 match {
  case portfolio_initial_margin_exta(name, amount, currency, more) => name
}

def portfolio_initial_margins: List[portfolio_initial_margin_ext[Unit]] =
  List(portfolio_initial_margin_exta[Unit](List(Char(true, false, true, false,
              true, false, true, false),
         Char(true, true, false, false, true, false, true, false),
         Char(false, false, true, false, false, false, true, false),
         Char(true, true, true, true, true, false, true, false),
         Char(true, false, false, true, false, false, true, false),
         Char(false, true, false, false, true, false, true, false),
         Char(true, true, false, false, true, false, true, false),
         Char(false, false, true, true, false, false, true, false),
         Char(true, true, false, false, true, true, false, false),
         Char(true, false, true, true, false, false, true, false),
         Char(true, true, true, true, true, false, true, false),
         Char(false, true, false, false, true, true, false, false),
         Char(true, false, false, true, true, false, true, false)),
    int_of_integer(BigInt(2000)), EUR, ()),
        portfolio_initial_margin_exta[Unit](List(Char(true, false, true, false,
               true, false, true, false),
          Char(true, true, false, false, true, false, true, false),
          Char(false, false, true, false, false, false, true, false)),
     uminus_int(int_of_integer(BigInt(1300000))), GBP, ()))

def get_amount_portfolio_initial_margin(asset_name: List[char]): real =
  Ratreal(of_int({
                   val initial_margins: List[portfolio_initial_margin_ext[Unit]]
                     = filter[portfolio_initial_margin_ext[Unit],
                               List[char]](portfolio_initial_margins,
    asset_name, ((a: portfolio_initial_margin_ext[Unit]) => namee[Unit](a)));
                   (if (nulla[portfolio_initial_margin_ext[Unit]](initial_margins))
                     zero_int
                     else amounta[Unit](nth[portfolio_initial_margin_ext[Unit]](initial_margins,
 zero_nat())))
                 }))

def amount[A](x0: portfolio_derivative_ext[A]): int = x0 match {
  case portfolio_derivative_exta(name, amount, currency, more) => amount
}

def get_amount_portfolio_derivative(asset_name: List[char]): real =
  Ratreal(of_int({
                   val derivatives: List[portfolio_derivative_ext[Unit]] =
                     filter[portfolio_derivative_ext[Unit],
                             List[char]](portfolio_derivatives, asset_name,
  ((a: portfolio_derivative_ext[Unit]) => namec[Unit](a)));
                   (if (nulla[portfolio_derivative_ext[Unit]](derivatives))
                     zero_int
                     else amount[Unit](nth[portfolio_derivative_ext[Unit]](derivatives,
                                    zero_nat())))
                 }))

def get_amount(asset_name: List[char]): real =
  minus_reala(minus_reala(get_amount_portfolio_derivative(asset_name),
                           get_amount_portfolio_initial_margin(asset_name)),
               get_amount_portfolio_variation_margin(asset_name))

def simulated_profit_loss(asset: List[char]): List[real] =
  (if (member[List[char]](currencies, asset))
    {
      val shocks: List[real] = get_shocks(asset)
      val x_amount: real = get_amount(asset);
      mapfun[real,
              real](((x: real) =>
                      times_reala(amount_in_euro(amount_in_euro(x,
                         get_currency(asset)),
          get_currency_number(asset)),
                                   x_amount)),
                     shocks)
    }
    else {
           val shocks: List[real] = get_shocks(asset)
           val is_sensitivity: Boolean = get_sensitivity(asset)
           val x_amount: real = get_amount(asset)
           val x_curr: nat = get_currency(asset)
           val base_level: real = get_base_level(asset)
           val is_relative: Boolean = get_relative(asset)
           val shift: real = get_shift(asset);
           mapfun[real,
                   real](((x: real) =>
                           profit_loss(x, is_sensitivity, x_amount, x_curr,
base_level, shift, is_relative)),
                          shocks)
         })

def numeral[A : numeral](x0: num): A = x0 match {
  case Bit1(n) => {
                    val m: A = numeral[A](n);
                    plus[A](plus[A](m, m), one[A])
                  }
  case Bit0(n) => {
                    val m: A = numeral[A](n);
                    plus[A](m, m)
                  }
  case One() => one[A]
}

def var_level[A : inverse : numeral]: A =
  divide[A](numeral[A](Bit1(Bit0(Bit0(One())))),
             numeral[A](Bit0(Bit1(Bit0(One())))))

def pairwise_sum(x0: List[real], x1: List[real]): List[real] = (x0, x1) match {
  case (Nil, Nil) => Nil
  case (xs :: x, ys :: y) => plus_reala(xs, ys) :: pairwise_sum(x, y)
  case (v :: va, Nil) => Nil
  case (Nil, v :: va) => Nil
}

def sum_up_list(x0: List[List[real]]): List[real] = x0 match {
  case Nil => Nil
  case List(xs) => xs
  case xs :: ys :: x => sum_up_list(pairwise_sum(xs, ys) :: x)
}

def asset_risk(local_risk_type: List[char]): real =
  {
    val holding_names: List[List[char]] =
      accumulate_holding_names(local_risk_type)
    val risk_list: List[real] =
      sum_up_list(mapfun[List[char],
                          List[real]](((a: List[char]) =>
simulated_profit_loss(a)),
                                       holding_names));
    percentile_impl(risk_list, var_level[real])
  }

} /* object foveSIMM */
