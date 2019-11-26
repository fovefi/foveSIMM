object Fun {

def id[A]: A => A = ((x: A) => x)

def comp[A, B, C](f: A => B, g: C => A): C => B = ((x: C) => f(g(x)))

} /* object Fun */

object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)
object equal {
  implicit def `Int.equal_int`: equal[Int.int] = new equal[Int.int] {
    val `HOL.equal` = (a: Int.int, b: Int.int) => Int.equal_inta(a, b)
  }
}

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Product_Type {

def fst[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def snd[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

def equal_prod[A : HOL.equal, B : HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => HOL.eq[A](x1, y1) && HOL.eq[B](x2, y2)
}

} /* object Product_Type */

object Orderings {

trait ord[A] {
  val `Orderings.less_eq`: (A, A) => Boolean
  val `Orderings.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`Orderings.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Orderings.less`(a, b)
object ord {
  implicit def `Real.ord_real`: ord[Real.real] = new ord[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
  }
}

trait preorder[A] extends ord[A] {
}
object preorder {
  implicit def `Real.preorder_real`: preorder[Real.real] = new
    preorder[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
  }
}

trait order[A] extends preorder[A] {
}
object order {
  implicit def `Real.order_real`: order[Real.real] = new order[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
  }
}

trait no_bot[A] extends order[A] {
}
object no_bot {
  implicit def `Real.no_bot_real`: no_bot[Real.real] = new no_bot[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
  }
}

trait no_top[A] extends order[A] {
}
object no_top {
  implicit def `Real.no_top_real`: no_top[Real.real] = new no_top[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
  }
}

trait linorder[A] extends order[A] {
}
object linorder {
  implicit def `Real.linorder_real`: linorder[Real.real] = new
    linorder[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
  }
}

trait dense_order[A] extends order[A] {
}
object dense_order {
  implicit def `Real.dense_order_real`: dense_order[Real.real] = new
    dense_order[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
  }
}

trait dense_linorder[A] extends dense_order[A] with linorder[A] {
}
object dense_linorder {
  implicit def `Real.dense_linorder_real`: dense_linorder[Real.real] = new
    dense_linorder[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
  }
}

trait unbounded_dense_linorder[A]
  extends dense_linorder[A] with no_bot[A] with no_top[A] {
}
object unbounded_dense_linorder {
  implicit def
    `Real.unbounded_dense_linorder_real`: unbounded_dense_linorder[Real.real] =
    new unbounded_dense_linorder[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
  }
}

} /* object Orderings */

object Semiring_Normalization {

trait comm_semiring_1_cancel_crossproduct[A]
  extends Rings.comm_semiring_1_cancel[A] {
}
object comm_semiring_1_cancel_crossproduct {
  implicit def
    `Real.comm_semiring_1_cancel_crossproduct_real`:
      comm_semiring_1_cancel_crossproduct[Real.real]
    = new comm_semiring_1_cancel_crossproduct[Real.real] {
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

} /* object Semiring_Normalization */

object Power {

trait power[A] extends Groups.one[A] with Groups.times[A] {
}
object power {
  implicit def `Real.power_real`: power[Real.real] = new power[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.one` = Real.one_reala
  }
}

} /* object Power */

object Nat {

trait semiring_char_0[A] extends Rings.semiring_1[A] {
}
object semiring_char_0 {
  implicit def `Real.semiring_char_0_real`: semiring_char_0[Real.real] = new
    semiring_char_0[Real.real] {
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ring_char_0[A] extends semiring_char_0[A] with Rings.ring_1[A] {
}
object ring_char_0 {
  implicit def `Real.ring_char_0_real`: ring_char_0[Real.real] = new
    ring_char_0[Real.real] {
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

abstract sealed class nat
final case class zero_nat() extends nat
final case class Suc(a: nat) extends nat

def one_nat: nat = Suc(zero_nat())

def plus_nat(x0: nat, n: nat): nat = (x0, n) match {
  case (Suc(m), n) => plus_nat(m, Suc(n))
  case (zero_nat(), n) => n
}

def of_nat_aux[A : Rings.semiring_1](inc: A => A, x1: nat, i: A): A =
  (inc, x1, i) match {
  case (inc, zero_nat(), i) => i
  case (inc, Suc(n), i) => of_nat_aux[A](inc, n, inc(i))
}

def of_nat[A : Rings.semiring_1](n: nat): A =
  of_nat_aux[A](((i: A) => Groups.plus[A](i, Groups.one[A])), n, Groups.zero[A])

} /* object Nat */

object Num {

trait numeral[A] extends Groups.one[A] with Groups.semigroup_add[A] {
}
object numeral {
  implicit def `Real.numeral_real`: numeral[Real.real] = new numeral[Real.real]
    {
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
    val `Groups.one` = Real.one_reala
  }
}

trait neg_numeral[A] extends Groups.group_add[A] with numeral[A] {
}
object neg_numeral {
  implicit def `Real.neg_numeral_real`: neg_numeral[Real.real] = new
    neg_numeral[Real.real] {
    val `Groups.one` = Real.one_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait semiring_numeral[A]
  extends Groups.monoid_mult[A] with numeral[A] with Rings.semiring[A] {
}
object semiring_numeral {
  implicit def `Real.semiring_numeral_real`: semiring_numeral[Real.real] = new
    semiring_numeral[Real.real] {
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
}

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

def BitM(x0: num): num = x0 match {
  case One() => One()
  case Bit0(n) => Bit1(BitM(n))
  case Bit1(n) => Bit1(Bit0(n))
}

def nat_of_num(x0: num): Nat.nat = x0 match {
  case Bit1(n) => {
                    val m: Nat.nat = nat_of_num(n);
                    Nat.Suc(Nat.plus_nat(m, m))
                  }
  case Bit0(n) => {
                    val m: Nat.nat = nat_of_num(n);
                    Nat.plus_nat(m, m)
                  }
  case One() => Nat.one_nat
}

def less_eq_num(x0: num, n: num): Boolean = (x0, n) match {
  case (Bit1(m), Bit0(n)) => less_num(m, n)
  case (Bit1(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit0(n)) => less_eq_num(m, n)
  case (Bit1(m), One()) => false
  case (Bit0(m), One()) => false
  case (One(), n) => true
}

def less_num(m: num, x1: num): Boolean = (m, x1) match {
  case (Bit1(m), Bit0(n)) => less_num(m, n)
  case (Bit1(m), Bit1(n)) => less_num(m, n)
  case (Bit0(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit0(n)) => less_num(m, n)
  case (One(), Bit1(n)) => true
  case (One(), Bit0(n)) => true
  case (m, One()) => false
}

def plus_num(x0: num, x1: num): num = (x0, x1) match {
  case (Bit1(m), Bit1(n)) => Bit0(plus_num(plus_num(m, n), One()))
  case (Bit1(m), Bit0(n)) => Bit1(plus_num(m, n))
  case (Bit1(m), One()) => Bit0(plus_num(m, One()))
  case (Bit0(m), Bit1(n)) => Bit1(plus_num(m, n))
  case (Bit0(m), Bit0(n)) => Bit0(plus_num(m, n))
  case (Bit0(m), One()) => Bit1(m)
  case (One(), Bit1(n)) => Bit0(plus_num(n, One()))
  case (One(), Bit0(n)) => Bit1(n)
  case (One(), One()) => Bit0(One())
}

def equal_num(x0: num, x1: num): Boolean = (x0, x1) match {
  case (Bit0(x2), Bit1(x3)) => false
  case (Bit1(x3), Bit0(x2)) => false
  case (One(), Bit1(x3)) => false
  case (Bit1(x3), One()) => false
  case (One(), Bit0(x2)) => false
  case (Bit0(x2), One()) => false
  case (Bit1(x3), Bit1(y3)) => equal_num(x3, y3)
  case (Bit0(x2), Bit0(y2)) => equal_num(x2, y2)
  case (One(), One()) => true
}

def times_num(m: num, n: num): num = (m, n) match {
  case (Bit1(m), Bit1(n)) =>
    Bit1(plus_num(plus_num(m, n), Bit0(times_num(m, n))))
  case (Bit1(m), Bit0(n)) => Bit0(times_num(Bit1(m), n))
  case (Bit0(m), Bit1(n)) => Bit0(times_num(m, Bit1(n)))
  case (Bit0(m), Bit0(n)) => Bit0(Bit0(times_num(m, n)))
  case (One(), n) => n
  case (m, One()) => m
}

} /* object Num */

object Groups {

trait plus[A] {
  val `Groups.plus`: (A, A) => A
}
def plus[A](a: A, b: A)(implicit A: plus[A]): A = A.`Groups.plus`(a, b)
object plus {
  implicit def `Real.plus_real`: plus[Real.real] = new plus[Real.real] {
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait semigroup_add[A] extends plus[A] {
}
object semigroup_add {
  implicit def `Real.semigroup_add_real`: semigroup_add[Real.real] = new
    semigroup_add[Real.real] {
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait cancel_semigroup_add[A] extends semigroup_add[A] {
}
object cancel_semigroup_add {
  implicit def `Real.cancel_semigroup_add_real`: cancel_semigroup_add[Real.real]
    = new cancel_semigroup_add[Real.real] {
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait zero[A] {
  val `Groups.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`Groups.zero`
object zero {
  implicit def `Real.zero_real`: zero[Real.real] = new zero[Real.real] {
    val `Groups.zero` = Real.zero_reala
  }
  implicit def `Int.zero_int`: zero[Int.int] = new zero[Int.int] {
    val `Groups.zero` = Int.zero_inta()
  }
}

trait monoid_add[A] extends semigroup_add[A] with zero[A] {
}
object monoid_add {
  implicit def `Real.monoid_add_real`: monoid_add[Real.real] = new
    monoid_add[Real.real] {
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait uminus[A] {
  val `Groups.uminus`: A => A
}
def uminus[A](a: A)(implicit A: uminus[A]): A = A.`Groups.uminus`(a)
object uminus {
  implicit def `Real.uminus_real`: uminus[Real.real] = new uminus[Real.real] {
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
  }
}

trait minus[A] {
  val `Groups.minus`: (A, A) => A
}
def minus[A](a: A, b: A)(implicit A: minus[A]): A = A.`Groups.minus`(a, b)
object minus {
  implicit def `Real.minus_real`: minus[Real.real] = new minus[Real.real] {
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
  }
}

trait group_add[A]
  extends cancel_semigroup_add[A] with minus[A] with monoid_add[A] with
    uminus[A]
  {
}
object group_add {
  implicit def `Real.group_add_real`: group_add[Real.real] = new
    group_add[Real.real] {
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait times[A] {
  val `Groups.times`: (A, A) => A
}
def times[A](a: A, b: A)(implicit A: times[A]): A = A.`Groups.times`(a, b)
object times {
  implicit def `Real.times_real`: times[Real.real] = new times[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
}

trait semigroup_mult[A] extends times[A] {
}
object semigroup_mult {
  implicit def `Real.semigroup_mult_real`: semigroup_mult[Real.real] = new
    semigroup_mult[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
}

trait monoid_mult[A] extends semigroup_mult[A] with Power.power[A] {
}
object monoid_mult {
  implicit def `Real.monoid_mult_real`: monoid_mult[Real.real] = new
    monoid_mult[Real.real] {
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
}

trait ab_semigroup_add[A] extends semigroup_add[A] {
}
object ab_semigroup_add {
  implicit def `Real.ab_semigroup_add_real`: ab_semigroup_add[Real.real] = new
    ab_semigroup_add[Real.real] {
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait cancel_ab_semigroup_add[A]
  extends ab_semigroup_add[A] with cancel_semigroup_add[A] with minus[A] {
}
object cancel_ab_semigroup_add {
  implicit def
    `Real.cancel_ab_semigroup_add_real`: cancel_ab_semigroup_add[Real.real] =
    new cancel_ab_semigroup_add[Real.real] {
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait comm_monoid_add[A] extends ab_semigroup_add[A] with monoid_add[A] {
}
object comm_monoid_add {
  implicit def `Real.comm_monoid_add_real`: comm_monoid_add[Real.real] = new
    comm_monoid_add[Real.real] {
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait cancel_comm_monoid_add[A]
  extends cancel_ab_semigroup_add[A] with comm_monoid_add[A] {
}
object cancel_comm_monoid_add {
  implicit def
    `Real.cancel_comm_monoid_add_real`: cancel_comm_monoid_add[Real.real] = new
    cancel_comm_monoid_add[Real.real] {
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ab_group_add[A] extends cancel_comm_monoid_add[A] with group_add[A] {
}
object ab_group_add {
  implicit def `Real.ab_group_add_real`: ab_group_add[Real.real] = new
    ab_group_add[Real.real] {
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ab_semigroup_mult[A] extends semigroup_mult[A] {
}
object ab_semigroup_mult {
  implicit def `Real.ab_semigroup_mult_real`: ab_semigroup_mult[Real.real] = new
    ab_semigroup_mult[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
}

trait comm_monoid_mult[A]
  extends ab_semigroup_mult[A] with monoid_mult[A] with Rings.dvd[A] {
}
object comm_monoid_mult {
  implicit def `Real.comm_monoid_mult_real`: comm_monoid_mult[Real.real] = new
    comm_monoid_mult[Real.real] {
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
}

trait ordered_ab_semigroup_add[A]
  extends ab_semigroup_add[A] with Orderings.order[A] {
}
object ordered_ab_semigroup_add {
  implicit def
    `Real.ordered_ab_semigroup_add_real`: ordered_ab_semigroup_add[Real.real] =
    new ordered_ab_semigroup_add[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait strict_ordered_ab_semigroup_add[A] extends ordered_ab_semigroup_add[A] {
}
object strict_ordered_ab_semigroup_add {
  implicit def
    `Real.strict_ordered_ab_semigroup_add_real`:
      strict_ordered_ab_semigroup_add[Real.real]
    = new strict_ordered_ab_semigroup_add[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ordered_cancel_ab_semigroup_add[A]
  extends cancel_ab_semigroup_add[A] with strict_ordered_ab_semigroup_add[A] {
}
object ordered_cancel_ab_semigroup_add {
  implicit def
    `Real.ordered_cancel_ab_semigroup_add_real`:
      ordered_cancel_ab_semigroup_add[Real.real]
    = new ordered_cancel_ab_semigroup_add[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ordered_ab_semigroup_add_imp_le[A]
  extends ordered_cancel_ab_semigroup_add[A] {
}
object ordered_ab_semigroup_add_imp_le {
  implicit def
    `Real.ordered_ab_semigroup_add_imp_le_real`:
      ordered_ab_semigroup_add_imp_le[Real.real]
    = new ordered_ab_semigroup_add_imp_le[Real.real] {
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait strict_ordered_comm_monoid_add[A]
  extends comm_monoid_add[A] with strict_ordered_ab_semigroup_add[A] {
}
object strict_ordered_comm_monoid_add {
  implicit def
    `Real.strict_ordered_comm_monoid_add_real`:
      strict_ordered_comm_monoid_add[Real.real]
    = new strict_ordered_comm_monoid_add[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ordered_comm_monoid_add[A]
  extends comm_monoid_add[A] with ordered_ab_semigroup_add[A] {
}
object ordered_comm_monoid_add {
  implicit def
    `Real.ordered_comm_monoid_add_real`: ordered_comm_monoid_add[Real.real] =
    new ordered_comm_monoid_add[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ordered_cancel_comm_monoid_add[A]
  extends ordered_cancel_ab_semigroup_add[A] with ordered_comm_monoid_add[A]
    with strict_ordered_comm_monoid_add[A]
  {
}
object ordered_cancel_comm_monoid_add {
  implicit def
    `Real.ordered_cancel_comm_monoid_add_real`:
      ordered_cancel_comm_monoid_add[Real.real]
    = new ordered_cancel_comm_monoid_add[Real.real] {
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ordered_ab_semigroup_monoid_add_imp_le[A]
  extends cancel_comm_monoid_add[A] with ordered_ab_semigroup_add_imp_le[A] with
    ordered_cancel_comm_monoid_add[A]
  {
}
object ordered_ab_semigroup_monoid_add_imp_le {
  implicit def
    `Real.ordered_ab_semigroup_monoid_add_imp_le_real`:
      ordered_ab_semigroup_monoid_add_imp_le[Real.real]
    = new ordered_ab_semigroup_monoid_add_imp_le[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ordered_ab_group_add[A]
  extends ab_group_add[A] with ordered_ab_semigroup_monoid_add_imp_le[A] {
}
object ordered_ab_group_add {
  implicit def `Real.ordered_ab_group_add_real`: ordered_ab_group_add[Real.real]
    = new ordered_ab_group_add[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait linordered_ab_semigroup_add[A]
  extends ordered_ab_semigroup_add[A] with Orderings.linorder[A] {
}
object linordered_ab_semigroup_add {
  implicit def
    `Real.linordered_ab_semigroup_add_real`:
      linordered_ab_semigroup_add[Real.real]
    = new linordered_ab_semigroup_add[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait linordered_cancel_ab_semigroup_add[A]
  extends linordered_ab_semigroup_add[A] with ordered_ab_semigroup_add_imp_le[A]
  {
}
object linordered_cancel_ab_semigroup_add {
  implicit def
    `Real.linordered_cancel_ab_semigroup_add_real`:
      linordered_cancel_ab_semigroup_add[Real.real]
    = new linordered_cancel_ab_semigroup_add[Real.real] {
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait linordered_ab_group_add[A]
  extends linordered_cancel_ab_semigroup_add[A] with ordered_ab_group_add[A] {
}
object linordered_ab_group_add {
  implicit def
    `Real.linordered_ab_group_add_real`: linordered_ab_group_add[Real.real] =
    new linordered_ab_group_add[Real.real] {
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait abs[A] {
  val `Groups.abs`: A => A
}
def abs[A](a: A)(implicit A: abs[A]): A = A.`Groups.abs`(a)
object abs {
  implicit def `Real.abs_real`: abs[Real.real] = new abs[Real.real] {
    val `Groups.abs` = (a: Real.real) => Real.abs_reala(a)
  }
}

trait ordered_ab_group_add_abs[A] extends abs[A] with ordered_ab_group_add[A] {
}
object ordered_ab_group_add_abs {
  implicit def
    `Real.ordered_ab_group_add_abs_real`: ordered_ab_group_add_abs[Real.real] =
    new ordered_ab_group_add_abs[Real.real] {
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
    val `Groups.abs` = (a: Real.real) => Real.abs_reala(a)
  }
}

trait one[A] {
  val `Groups.one`: A
}
def one[A](implicit A: one[A]): A = A.`Groups.one`
object one {
  implicit def `Real.one_real`: one[Real.real] = new one[Real.real] {
    val `Groups.one` = Real.one_reala
  }
  implicit def `Int.one_int`: one[Int.int] = new one[Int.int] {
    val `Groups.one` = Int.one_inta
  }
}

trait sgn[A] {
  val `Groups.sgn`: A => A
}
def sgn[A](a: A)(implicit A: sgn[A]): A = A.`Groups.sgn`(a)
object sgn {
  implicit def `Real.sgn_real`: sgn[Real.real] = new sgn[Real.real] {
    val `Groups.sgn` = (a: Real.real) => Real.sgn_reala(a)
  }
}

} /* object Groups */

object Rings {

trait dvd[A] extends Groups.times[A] {
}
object dvd {
  implicit def `Real.dvd_real`: dvd[Real.real] = new dvd[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
}

trait mult_zero[A] extends Groups.times[A] with Groups.zero[A] {
}
object mult_zero {
  implicit def `Real.mult_zero_real`: mult_zero[Real.real] = new
    mult_zero[Real.real] {
    val `Groups.zero` = Real.zero_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
}

trait semiring[A]
  extends Groups.ab_semigroup_add[A] with Groups.semigroup_mult[A] {
}
object semiring {
  implicit def `Real.semiring_real`: semiring[Real.real] = new
    semiring[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait semiring_0[A]
  extends Groups.comm_monoid_add[A] with mult_zero[A] with semiring[A] {
}
object semiring_0 {
  implicit def `Real.semiring_0_real`: semiring_0[Real.real] = new
    semiring_0[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait semiring_no_zero_divisors[A] extends semiring_0[A] {
}
object semiring_no_zero_divisors {
  implicit def
    `Real.semiring_no_zero_divisors_real`: semiring_no_zero_divisors[Real.real]
    = new semiring_no_zero_divisors[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait zero_neq_one[A] extends Groups.one[A] with Groups.zero[A] {
}
object zero_neq_one {
  implicit def `Real.zero_neq_one_real`: zero_neq_one[Real.real] = new
    zero_neq_one[Real.real] {
    val `Groups.zero` = Real.zero_reala
    val `Groups.one` = Real.one_reala
  }
  implicit def `Int.zero_neq_one_int`: zero_neq_one[Int.int] = new
    zero_neq_one[Int.int] {
    val `Groups.zero` = Int.zero_inta()
    val `Groups.one` = Int.one_inta
  }
}

trait semiring_1[A]
  extends Num.semiring_numeral[A] with semiring_0[A] with zero_neq_one[A] {
}
object semiring_1 {
  implicit def `Real.semiring_1_real`: semiring_1[Real.real] = new
    semiring_1[Real.real] {
    val `Groups.zero` = Real.zero_reala
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait semiring_1_no_zero_divisors[A]
  extends semiring_1[A] with semiring_no_zero_divisors[A] {
}
object semiring_1_no_zero_divisors {
  implicit def
    `Real.semiring_1_no_zero_divisors_real`:
      semiring_1_no_zero_divisors[Real.real]
    = new semiring_1_no_zero_divisors[Real.real] {
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait semiring_0_cancel[A]
  extends Groups.cancel_comm_monoid_add[A] with semiring_0[A] {
}
object semiring_0_cancel {
  implicit def `Real.semiring_0_cancel_real`: semiring_0_cancel[Real.real] = new
    semiring_0_cancel[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait comm_semiring[A] extends Groups.ab_semigroup_mult[A] with semiring[A] {
}
object comm_semiring {
  implicit def `Real.comm_semiring_real`: comm_semiring[Real.real] = new
    comm_semiring[Real.real] {
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
}

trait comm_semiring_0[A] extends comm_semiring[A] with semiring_0[A] {
}
object comm_semiring_0 {
  implicit def `Real.comm_semiring_0_real`: comm_semiring_0[Real.real] = new
    comm_semiring_0[Real.real] {
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
}

trait comm_semiring_0_cancel[A]
  extends comm_semiring_0[A] with semiring_0_cancel[A] {
}
object comm_semiring_0_cancel {
  implicit def
    `Real.comm_semiring_0_cancel_real`: comm_semiring_0_cancel[Real.real] = new
    comm_semiring_0_cancel[Real.real] {
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
}

trait semiring_1_cancel[A] extends semiring_0_cancel[A] with semiring_1[A] {
}
object semiring_1_cancel {
  implicit def `Real.semiring_1_cancel_real`: semiring_1_cancel[Real.real] = new
    semiring_1_cancel[Real.real] {
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait comm_semiring_1[A]
  extends Groups.comm_monoid_mult[A] with comm_semiring_0[A] with semiring_1[A]
  {
}
object comm_semiring_1 {
  implicit def `Real.comm_semiring_1_real`: comm_semiring_1[Real.real] = new
    comm_semiring_1[Real.real] {
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
}

trait comm_semiring_1_cancel[A]
  extends comm_semiring_0_cancel[A] with comm_semiring_1[A] with
    semiring_1_cancel[A]
  {
}
object comm_semiring_1_cancel {
  implicit def
    `Real.comm_semiring_1_cancel_real`: comm_semiring_1_cancel[Real.real] = new
    comm_semiring_1_cancel[Real.real] {
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait semidom[A]
  extends comm_semiring_1_cancel[A] with semiring_1_no_zero_divisors[A] {
}
object semidom {
  implicit def `Real.semidom_real`: semidom[Real.real] = new semidom[Real.real]
    {
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait semiring_no_zero_divisors_cancel[A] extends semiring_no_zero_divisors[A] {
}
object semiring_no_zero_divisors_cancel {
  implicit def
    `Real.semiring_no_zero_divisors_cancel_real`:
      semiring_no_zero_divisors_cancel[Real.real]
    = new semiring_no_zero_divisors_cancel[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ring[A] extends Groups.ab_group_add[A] with semiring_0_cancel[A] {
}
object ring {
  implicit def `Real.ring_real`: ring[Real.real] = new ring[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ring_no_zero_divisors[A]
  extends ring[A] with semiring_no_zero_divisors_cancel[A] {
}
object ring_no_zero_divisors {
  implicit def
    `Real.ring_no_zero_divisors_real`: ring_no_zero_divisors[Real.real] = new
    ring_no_zero_divisors[Real.real] {
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ring_1[A]
  extends Num.neg_numeral[A] with ring[A] with semiring_1_cancel[A] {
}
object ring_1 {
  implicit def `Real.ring_1_real`: ring_1[Real.real] = new ring_1[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.one` = Real.one_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ring_1_no_zero_divisors[A]
  extends ring_1[A] with ring_no_zero_divisors[A] with
    semiring_1_no_zero_divisors[A]
  {
}
object ring_1_no_zero_divisors {
  implicit def
    `Real.ring_1_no_zero_divisors_real`: ring_1_no_zero_divisors[Real.real] =
    new ring_1_no_zero_divisors[Real.real] {
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait comm_ring[A] extends comm_semiring_0_cancel[A] with ring[A] {
}
object comm_ring {
  implicit def `Real.comm_ring_real`: comm_ring[Real.real] = new
    comm_ring[Real.real] {
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait comm_ring_1[A]
  extends comm_ring[A] with comm_semiring_1_cancel[A] with ring_1[A] {
}
object comm_ring_1 {
  implicit def `Real.comm_ring_1_real`: comm_ring_1[Real.real] = new
    comm_ring_1[Real.real] {
    val `Groups.one` = Real.one_reala
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait idom[A]
  extends comm_ring_1[A] with ring_1_no_zero_divisors[A] with semidom[A] with
    Semiring_Normalization.comm_semiring_1_cancel_crossproduct[A]
  {
}
object idom {
  implicit def `Real.idom_real`: idom[Real.real] = new idom[Real.real] {
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait abs_if[A]
  extends Groups.abs[A] with Groups.minus[A] with Groups.uminus[A] with
    Groups.zero[A] with Orderings.ord[A]
  {
}
object abs_if {
  implicit def `Real.abs_if_real`: abs_if[Real.real] = new abs_if[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.abs` = (a: Real.real) => Real.abs_reala(a)
  }
}

trait divide[A] {
  val `Rings.divide`: (A, A) => A
}
def divide[A](a: A, b: A)(implicit A: divide[A]): A = A.`Rings.divide`(a, b)
object divide {
  implicit def `Real.divide_real`: divide[Real.real] = new divide[Real.real] {
    val `Rings.divide` = (a: Real.real, b: Real.real) => Real.divide_reala(a, b)
  }
}

trait semidom_divide[A]
  extends divide[A] with semidom[A] with semiring_no_zero_divisors_cancel[A] {
}
object semidom_divide {
  implicit def `Real.semidom_divide_real`: semidom_divide[Real.real] = new
    semidom_divide[Real.real] {
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
    val `Rings.divide` = (a: Real.real, b: Real.real) => Real.divide_reala(a, b)
  }
}

trait idom_divide[A] extends idom[A] with semidom_divide[A] {
}
object idom_divide {
  implicit def `Real.idom_divide_real`: idom_divide[Real.real] = new
    idom_divide[Real.real] {
    val `Rings.divide` = (a: Real.real, b: Real.real) => Real.divide_reala(a, b)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait idom_abs_sgn[A] extends Groups.abs[A] with Groups.sgn[A] with idom[A] {
}
object idom_abs_sgn {
  implicit def `Real.idom_abs_sgn_real`: idom_abs_sgn[Real.real] = new
    idom_abs_sgn[Real.real] {
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
    val `Groups.sgn` = (a: Real.real) => Real.sgn_reala(a)
    val `Groups.abs` = (a: Real.real) => Real.abs_reala(a)
  }
}

trait ordered_semiring[A]
  extends Groups.ordered_comm_monoid_add[A] with semiring[A] {
}
object ordered_semiring {
  implicit def `Real.ordered_semiring_real`: ordered_semiring[Real.real] = new
    ordered_semiring[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ordered_semiring_0[A] extends ordered_semiring[A] with semiring_0[A] {
}
object ordered_semiring_0 {
  implicit def `Real.ordered_semiring_0_real`: ordered_semiring_0[Real.real] =
    new ordered_semiring_0[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ordered_cancel_semiring[A]
  extends ordered_semiring_0[A] with semiring_0_cancel[A] {
}
object ordered_cancel_semiring {
  implicit def
    `Real.ordered_cancel_semiring_real`: ordered_cancel_semiring[Real.real] =
    new ordered_cancel_semiring[Real.real] {
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ordered_ring[A]
  extends Groups.ordered_ab_group_add[A] with ordered_cancel_semiring[A] with
    ring[A]
  {
}
object ordered_ring {
  implicit def `Real.ordered_ring_real`: ordered_ring[Real.real] = new
    ordered_ring[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait zero_less_one[A]
  extends Groups.one[A] with Groups.zero[A] with Orderings.order[A] {
}
object zero_less_one {
  implicit def `Real.zero_less_one_real`: zero_less_one[Real.real] = new
    zero_less_one[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.one` = Real.one_reala
  }
}

trait linordered_semiring[A]
  extends Groups.linordered_cancel_ab_semigroup_add[A] with
    Groups.ordered_ab_semigroup_monoid_add_imp_le[A] with
    ordered_cancel_semiring[A]
  {
}
object linordered_semiring {
  implicit def `Real.linordered_semiring_real`: linordered_semiring[Real.real] =
    new linordered_semiring[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait linordered_semiring_strict[A] extends linordered_semiring[A] {
}
object linordered_semiring_strict {
  implicit def
    `Real.linordered_semiring_strict_real`:
      linordered_semiring_strict[Real.real]
    = new linordered_semiring_strict[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait linordered_semiring_1[A]
  extends linordered_semiring[A] with semiring_1[A] with zero_less_one[A] {
}
object linordered_semiring_1 {
  implicit def
    `Real.linordered_semiring_1_real`: linordered_semiring_1[Real.real] = new
    linordered_semiring_1[Real.real] {
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait linordered_semiring_1_strict[A]
  extends linordered_semiring_1[A] with linordered_semiring_strict[A] {
}
object linordered_semiring_1_strict {
  implicit def
    `Real.linordered_semiring_1_strict_real`:
      linordered_semiring_1_strict[Real.real]
    = new linordered_semiring_1_strict[Real.real] {
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait linordered_ring[A]
  extends Groups.linordered_ab_group_add[A] with
    Groups.ordered_ab_group_add_abs[A] with abs_if[A] with
    linordered_semiring[A] with ordered_ring[A]
  {
}
object linordered_ring {
  implicit def `Real.linordered_ring_real`: linordered_ring[Real.real] = new
    linordered_ring[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.abs` = (a: Real.real) => Real.abs_reala(a)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait linordered_ring_strict[A]
  extends linordered_ring[A] with linordered_semiring_strict[A] with
    ring_no_zero_divisors[A]
  {
}
object linordered_ring_strict {
  implicit def
    `Real.linordered_ring_strict_real`: linordered_ring_strict[Real.real] = new
    linordered_ring_strict[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.abs` = (a: Real.real) => Real.abs_reala(a)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ordered_comm_semiring[A]
  extends comm_semiring_0[A] with ordered_semiring[A] {
}
object ordered_comm_semiring {
  implicit def
    `Real.ordered_comm_semiring_real`: ordered_comm_semiring[Real.real] = new
    ordered_comm_semiring[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
}

trait ordered_cancel_comm_semiring[A]
  extends comm_semiring_0_cancel[A] with ordered_cancel_semiring[A] with
    ordered_comm_semiring[A]
  {
}
object ordered_cancel_comm_semiring {
  implicit def
    `Real.ordered_cancel_comm_semiring_real`:
      ordered_cancel_comm_semiring[Real.real]
    = new ordered_cancel_comm_semiring[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait linordered_comm_semiring_strict[A]
  extends linordered_semiring_strict[A] with ordered_cancel_comm_semiring[A] {
}
object linordered_comm_semiring_strict {
  implicit def
    `Real.linordered_comm_semiring_strict_real`:
      linordered_comm_semiring_strict[Real.real]
    = new linordered_comm_semiring_strict[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait linordered_nonzero_semiring[A]
  extends Nat.semiring_char_0[A] with Orderings.linorder[A] with
    comm_semiring_1[A] with ordered_comm_semiring[A] with zero_less_one[A]
  {
}
object linordered_nonzero_semiring {
  implicit def
    `Real.linordered_nonzero_semiring_real`:
      linordered_nonzero_semiring[Real.real]
    = new linordered_nonzero_semiring[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait linordered_semidom[A]
  extends linordered_comm_semiring_strict[A] with linordered_nonzero_semiring[A]
    with semidom[A]
  {
}
object linordered_semidom {
  implicit def `Real.linordered_semidom_real`: linordered_semidom[Real.real] =
    new linordered_semidom[Real.real] {
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ordered_comm_ring[A]
  extends comm_ring[A] with ordered_cancel_comm_semiring[A] with ordered_ring[A]
  {
}
object ordered_comm_ring {
  implicit def `Real.ordered_comm_ring_real`: ordered_comm_ring[Real.real] = new
    ordered_comm_ring[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait ordered_ring_abs[A]
  extends Groups.ordered_ab_group_add_abs[A] with ordered_ring[A] {
}
object ordered_ring_abs {
  implicit def `Real.ordered_ring_abs_real`: ordered_ring_abs[Real.real] = new
    ordered_ring_abs[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.abs` = (a: Real.real) => Real.abs_reala(a)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait linordered_idom[A]
  extends Nat.ring_char_0[A] with idom_abs_sgn[A] with linordered_ring_strict[A]
    with linordered_semidom[A] with linordered_semiring_1_strict[A] with
    ordered_comm_ring[A] with ordered_ring_abs[A]
  {
}
object linordered_idom {
  implicit def `Real.linordered_idom_real`: linordered_idom[Real.real] = new
    linordered_idom[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.abs` = (a: Real.real) => Real.abs_reala(a)
    val `Groups.sgn` = (a: Real.real) => Real.sgn_reala(a)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

def of_bool[A : zero_neq_one](x0: Boolean): A = x0 match {
  case true => Groups.one[A]
  case false => Groups.zero[A]
}

} /* object Rings */

object Int {

abstract sealed class int
final case class zero_inta() extends int
final case class Pos(a: Num.num) extends int
final case class Neg(a: Num.num) extends int

def equal_inta(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => Num.equal_num(k, l)
  case (Neg(k), Pos(l)) => false
  case (Neg(k), zero_inta()) => false
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => Num.equal_num(k, l)
  case (Pos(k), zero_inta()) => false
  case (zero_inta(), Neg(l)) => false
  case (zero_inta(), Pos(l)) => false
  case (zero_inta(), zero_inta()) => true
}

def one_inta: int = Pos(Num.One())

def dup(x0: int): int = x0 match {
  case Neg(n) => Neg(Num.Bit0(n))
  case Pos(n) => Pos(Num.Bit0(n))
  case zero_inta() => zero_inta()
}

def nat(x0: int): Nat.nat = x0 match {
  case Pos(k) => Num.nat_of_num(k)
  case zero_inta() => Nat.zero_nat()
  case Neg(k) => Nat.zero_nat()
}

def uminus_int(x0: int): int = x0 match {
  case Neg(m) => Pos(m)
  case Pos(m) => Neg(m)
  case zero_inta() => zero_inta()
}

def minus_int(k: int, l: int): int = (k, l) match {
  case (Neg(m), Neg(n)) => sub(n, m)
  case (Neg(m), Pos(n)) => Neg(Num.plus_num(m, n))
  case (Pos(m), Neg(n)) => Pos(Num.plus_num(m, n))
  case (Pos(m), Pos(n)) => sub(m, n)
  case (zero_inta(), l) => uminus_int(l)
  case (k, zero_inta()) => k
}

def plus_int(k: int, l: int): int = (k, l) match {
  case (Neg(m), Neg(n)) => Neg(Num.plus_num(m, n))
  case (Neg(m), Pos(n)) => sub(n, m)
  case (Pos(m), Neg(n)) => sub(m, n)
  case (Pos(m), Pos(n)) => Pos(Num.plus_num(m, n))
  case (zero_inta(), l) => l
  case (k, zero_inta()) => k
}

def sub(x0: Num.num, x1: Num.num): int = (x0, x1) match {
  case (Num.Bit0(m), Num.Bit1(n)) => minus_int(dup(sub(m, n)), one_inta)
  case (Num.Bit1(m), Num.Bit0(n)) => plus_int(dup(sub(m, n)), one_inta)
  case (Num.Bit1(m), Num.Bit1(n)) => dup(sub(m, n))
  case (Num.Bit0(m), Num.Bit0(n)) => dup(sub(m, n))
  case (Num.One(), Num.Bit1(n)) => Neg(Num.Bit0(n))
  case (Num.One(), Num.Bit0(n)) => Neg(Num.BitM(n))
  case (Num.Bit1(m), Num.One()) => Pos(Num.Bit0(m))
  case (Num.Bit0(m), Num.One()) => Pos(Num.BitM(m))
  case (Num.One(), Num.One()) => zero_inta()
}

def less_int(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => Num.less_num(l, k)
  case (Neg(k), Pos(l)) => true
  case (Neg(k), zero_inta()) => true
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => Num.less_num(k, l)
  case (Pos(k), zero_inta()) => false
  case (zero_inta(), Neg(l)) => false
  case (zero_inta(), Pos(l)) => true
  case (zero_inta(), zero_inta()) => false
}

def abs_int(i: int): int = (if (less_int(i, zero_inta())) uminus_int(i) else i)

def sgn_int(i: int): int =
  (if (equal_inta(i, zero_inta())) zero_inta()
    else (if (less_int(zero_inta(), i)) one_inta else uminus_int(one_inta)))

def less_eq_int(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => Num.less_eq_num(l, k)
  case (Neg(k), Pos(l)) => true
  case (Neg(k), zero_inta()) => true
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => Num.less_eq_num(k, l)
  case (Pos(k), zero_inta()) => false
  case (zero_inta(), Neg(l)) => false
  case (zero_inta(), Pos(l)) => true
  case (zero_inta(), zero_inta()) => true
}

def times_int(k: int, l: int): int = (k, l) match {
  case (Neg(m), Neg(n)) => Pos(Num.times_num(m, n))
  case (Neg(m), Pos(n)) => Neg(Num.times_num(m, n))
  case (Pos(m), Neg(n)) => Neg(Num.times_num(m, n))
  case (Pos(m), Pos(n)) => Pos(Num.times_num(m, n))
  case (zero_inta(), l) => zero_inta()
  case (k, zero_inta()) => zero_inta()
}

} /* object Int */

object Divides {

def adjust_div(x0: (Int.int, Int.int)): Int.int = x0 match {
  case (q, r) =>
    Int.plus_int(q, Rings.of_bool[Int.int](! (Int.equal_inta(r,
                      Int.zero_inta()))))
}

def adjust_mod(l: Int.int, r: Int.int): Int.int =
  (if (Int.equal_inta(r, Int.zero_inta())) Int.zero_inta()
    else Int.minus_int(l, r))

def divmod_step_int(l: Num.num, x1: (Int.int, Int.int)): (Int.int, Int.int) =
  (l, x1) match {
  case (l, (q, r)) =>
    (if (Int.less_eq_int(Int.Pos(l), r))
      (Int.plus_int(Int.times_int(Int.Pos(Num.Bit0(Num.One())), q),
                     Int.one_inta),
        Int.minus_int(r, Int.Pos(l)))
      else (Int.times_int(Int.Pos(Num.Bit0(Num.One())), q), r))
}

def divmod_int(x0: Num.num, x1: Num.num): (Int.int, Int.int) = (x0, x1) match {
  case (Num.Bit1(m), Num.Bit1(n)) =>
    (if (Num.less_num(m, n)) (Int.zero_inta(), Int.Pos(Num.Bit1(m)))
      else divmod_step_int(Num.Bit1(n),
                            divmod_int(Num.Bit1(m), Num.Bit0(Num.Bit1(n)))))
  case (Num.Bit0(m), Num.Bit1(n)) =>
    (if (Num.less_eq_num(m, n)) (Int.zero_inta(), Int.Pos(Num.Bit0(m)))
      else divmod_step_int(Num.Bit1(n),
                            divmod_int(Num.Bit0(m), Num.Bit0(Num.Bit1(n)))))
  case (Num.Bit1(m), Num.Bit0(n)) =>
    {
      val (q, r): (Int.int, Int.int) = divmod_int(m, n);
      (q, Int.plus_int(Int.times_int(Int.Pos(Num.Bit0(Num.One())), r),
                        Int.one_inta))
    }
  case (Num.Bit0(m), Num.Bit0(n)) =>
    {
      val (q, r): (Int.int, Int.int) = divmod_int(m, n);
      (q, Int.times_int(Int.Pos(Num.Bit0(Num.One())), r))
    }
  case (Num.One(), Num.Bit1(n)) => (Int.zero_inta(), Int.Pos(Num.One()))
  case (Num.One(), Num.Bit0(n)) => (Int.zero_inta(), Int.Pos(Num.One()))
  case (Num.Bit1(m), Num.One()) => (Int.Pos(Num.Bit1(m)), Int.zero_inta())
  case (Num.Bit0(m), Num.One()) => (Int.Pos(Num.Bit0(m)), Int.zero_inta())
  case (Num.One(), Num.One()) => (Int.Pos(Num.One()), Int.zero_inta())
}

} /* object Divides */

object Euclidean_Division {

def divide_int(k: Int.int, ka: Int.int): Int.int = (k, ka) match {
  case (Int.Neg(m), Int.Neg(n)) =>
    Product_Type.fst[Int.int, Int.int](Divides.divmod_int(m, n))
  case (Int.Pos(m), Int.Neg(n)) =>
    Int.uminus_int(Divides.adjust_div(Divides.divmod_int(m, n)))
  case (Int.Neg(m), Int.Pos(n)) =>
    Int.uminus_int(Divides.adjust_div(Divides.divmod_int(m, n)))
  case (Int.Pos(m), Int.Pos(n)) =>
    Product_Type.fst[Int.int, Int.int](Divides.divmod_int(m, n))
  case (k, Int.Neg(Num.One())) => Int.uminus_int(k)
  case (k, Int.Pos(Num.One())) => k
  case (Int.zero_inta(), k) => Int.zero_inta()
  case (k, Int.zero_inta()) => Int.zero_inta()
}

def modulo_int(k: Int.int, ka: Int.int): Int.int = (k, ka) match {
  case (Int.Neg(m), Int.Neg(n)) =>
    Int.uminus_int(Product_Type.snd[Int.int, Int.int](Divides.divmod_int(m, n)))
  case (Int.Pos(m), Int.Neg(n)) =>
    Int.uminus_int(Divides.adjust_mod(Int.Pos(n),
                                       Product_Type.snd[Int.int,
                 Int.int](Divides.divmod_int(m, n))))
  case (Int.Neg(m), Int.Pos(n)) =>
    Divides.adjust_mod(Int.Pos(n),
                        Product_Type.snd[Int.int,
  Int.int](Divides.divmod_int(m, n)))
  case (Int.Pos(m), Int.Pos(n)) =>
    Product_Type.snd[Int.int, Int.int](Divides.divmod_int(m, n))
  case (k, Int.Neg(Num.One())) => Int.zero_inta()
  case (k, Int.Pos(Num.One())) => Int.zero_inta()
  case (Int.zero_inta(), k) => Int.zero_inta()
  case (k, Int.zero_inta()) => k
}

} /* object Euclidean_Division */

object GCD {

def gcd_int(k: Int.int, l: Int.int): Int.int =
  Int.abs_int((if (Int.equal_inta(l, Int.zero_inta())) k
                else gcd_int(l, Euclidean_Division.modulo_int(Int.abs_int(k),
                       Int.abs_int(l)))))

} /* object GCD */

object Rat {

abstract sealed class rat
final case class Frct(a: (Int.int, Int.int)) extends rat

def of_int(a: Int.int): rat = Frct((a, Int.one_inta))

def normalize(p: (Int.int, Int.int)): (Int.int, Int.int) =
  (if (Int.less_int(Int.zero_inta(), Product_Type.snd[Int.int, Int.int](p)))
    {
      val a: Int.int =
        GCD.gcd_int(Product_Type.fst[Int.int, Int.int](p),
                     Product_Type.snd[Int.int, Int.int](p));
      (Euclidean_Division.divide_int(Product_Type.fst[Int.int, Int.int](p), a),
        Euclidean_Division.divide_int(Product_Type.snd[Int.int, Int.int](p), a))
    }
    else (if (Int.equal_inta(Product_Type.snd[Int.int, Int.int](p),
                              Int.zero_inta()))
           (Int.zero_inta(), Int.one_inta)
           else {
                  val a: Int.int =
                    Int.uminus_int(GCD.gcd_int(Product_Type.fst[Int.int,
                         Int.int](p),
        Product_Type.snd[Int.int, Int.int](p)));
                  (Euclidean_Division.divide_int(Product_Type.fst[Int.int,
                           Int.int](p),
          a),
                    Euclidean_Division.divide_int(Product_Type.snd[Int.int,
                            Int.int](p),
           a))
                }))

def quotient_of(x0: rat): (Int.int, Int.int) = x0 match {
  case Frct(x) => x
}

def one_rat: rat = Frct((Int.one_inta, Int.one_inta))

def less_rat(p: rat, q: rat): Boolean =
  {
    val a: (Int.int, Int.int) = quotient_of(p)
    val (aa, c): (Int.int, Int.int) = a
    val b: (Int.int, Int.int) = quotient_of(q)
    val (ba, d): (Int.int, Int.int) = b;
    Int.less_int(Int.times_int(aa, d), Int.times_int(c, ba))
  }

def plus_rat(p: rat, q: rat): rat =
  Frct({
         val a: (Int.int, Int.int) = quotient_of(p)
         val (aa, c): (Int.int, Int.int) = a
         val b: (Int.int, Int.int) = quotient_of(q)
         val (ba, d): (Int.int, Int.int) = b;
         normalize((Int.plus_int(Int.times_int(aa, d), Int.times_int(ba, c)),
                     Int.times_int(c, d)))
       })

def zero_rat: rat = Frct((Int.zero_inta(), Int.one_inta))

def equal_rat(a: rat, b: rat): Boolean =
  Product_Type.equal_prod[Int.int, Int.int](quotient_of(a), quotient_of(b))

def minus_rat(p: rat, q: rat): rat =
  Frct({
         val a: (Int.int, Int.int) = quotient_of(p)
         val (aa, c): (Int.int, Int.int) = a
         val b: (Int.int, Int.int) = quotient_of(q)
         val (ba, d): (Int.int, Int.int) = b;
         normalize((Int.minus_int(Int.times_int(aa, d), Int.times_int(ba, c)),
                     Int.times_int(c, d)))
       })

def less_eq_rat(p: rat, q: rat): Boolean =
  {
    val a: (Int.int, Int.int) = quotient_of(p)
    val (aa, c): (Int.int, Int.int) = a
    val b: (Int.int, Int.int) = quotient_of(q)
    val (ba, d): (Int.int, Int.int) = b;
    Int.less_eq_int(Int.times_int(aa, d), Int.times_int(c, ba))
  }

def times_rat(p: rat, q: rat): rat =
  Frct({
         val a: (Int.int, Int.int) = quotient_of(p)
         val (aa, c): (Int.int, Int.int) = a
         val b: (Int.int, Int.int) = quotient_of(q)
         val (ba, d): (Int.int, Int.int) = b;
         normalize((Int.times_int(aa, ba), Int.times_int(c, d)))
       })

def divide_rat(p: rat, q: rat): rat =
  Frct({
         val a: (Int.int, Int.int) = quotient_of(p)
         val (aa, c): (Int.int, Int.int) = a
         val b: (Int.int, Int.int) = quotient_of(q)
         val (ba, d): (Int.int, Int.int) = b;
         normalize((Int.times_int(aa, d), Int.times_int(c, ba)))
       })

def uminus_rat(p: rat): rat = Frct({
                                     val a: (Int.int, Int.int) = quotient_of(p)
                                     val (aa, b): (Int.int, Int.int) = a;
                                     (Int.uminus_int(aa), b)
                                   })

def inverse_rat(p: rat): rat =
  Frct({
         val a: (Int.int, Int.int) = quotient_of(p)
         val (aa, b): (Int.int, Int.int) = a;
         (if (Int.equal_inta(aa, Int.zero_inta()))
           (Int.zero_inta(), Int.one_inta)
           else (Int.times_int(Int.sgn_int(aa), b), Int.abs_int(aa)))
       })

def floor_rat(p: rat): Int.int = {
                                   val a: (Int.int, Int.int) = quotient_of(p)
                                   val (aa, b): (Int.int, Int.int) = a;
                                   Euclidean_Division.divide_int(aa, b)
                                 }

} /* object Rat */

object Fields {

trait inverse[A] extends Rings.divide[A] {
  val `Fields.inverse`: A => A
}
def inverse[A](a: A)(implicit A: inverse[A]): A = A.`Fields.inverse`(a)
object inverse {
  implicit def `Real.inverse_real`: inverse[Real.real] = new inverse[Real.real]
    {
    val `Fields.inverse` = (a: Real.real) => Real.inverse_reala(a)
    val `Rings.divide` = (a: Real.real, b: Real.real) => Real.divide_reala(a, b)
  }
}

trait division_ring[A] extends inverse[A] with Rings.ring_1_no_zero_divisors[A]
  {
}
object division_ring {
  implicit def `Real.division_ring_real`: division_ring[Real.real] = new
    division_ring[Real.real] {
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
    val `Fields.inverse` = (a: Real.real) => Real.inverse_reala(a)
    val `Rings.divide` = (a: Real.real, b: Real.real) => Real.divide_reala(a, b)
  }
}

trait field[A] extends division_ring[A] with Rings.idom_divide[A] {
}
object field {
  implicit def `Real.field_real`: field[Real.real] = new field[Real.real] {
    val `Fields.inverse` = (a: Real.real) => Real.inverse_reala(a)
    val `Rings.divide` = (a: Real.real, b: Real.real) => Real.divide_reala(a, b)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait field_char_0[A] extends field[A] with Nat.ring_char_0[A] {
}
object field_char_0 {
  implicit def `Real.field_char_0_real`: field_char_0[Real.real] = new
    field_char_0[Real.real] {
    val `Fields.inverse` = (a: Real.real) => Real.inverse_reala(a)
    val `Rings.divide` = (a: Real.real, b: Real.real) => Real.divide_reala(a, b)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait field_abs_sgn[A] extends field[A] with Rings.idom_abs_sgn[A] {
}
object field_abs_sgn {
  implicit def `Real.field_abs_sgn_real`: field_abs_sgn[Real.real] = new
    field_abs_sgn[Real.real] {
    val `Groups.abs` = (a: Real.real) => Real.abs_reala(a)
    val `Groups.sgn` = (a: Real.real) => Real.sgn_reala(a)
    val `Fields.inverse` = (a: Real.real) => Real.inverse_reala(a)
    val `Rings.divide` = (a: Real.real, b: Real.real) => Real.divide_reala(a, b)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait linordered_field[A]
  extends field_abs_sgn[A] with field_char_0[A] with
    Orderings.unbounded_dense_linorder[A] with Rings.linordered_idom[A]
  {
}
object linordered_field {
  implicit def `Real.linordered_field_real`: linordered_field[Real.real] = new
    linordered_field[Real.real] {
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.abs` = (a: Real.real) => Real.abs_reala(a)
    val `Groups.sgn` = (a: Real.real) => Real.sgn_reala(a)
    val `Fields.inverse` = (a: Real.real) => Real.inverse_reala(a)
    val `Rings.divide` = (a: Real.real, b: Real.real) => Real.divide_reala(a, b)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

} /* object Fields */

object Archimedean_Field {

trait archimedean_field[A] extends Fields.linordered_field[A] {
}
object archimedean_field {
  implicit def `Real.archimedean_field_real`: archimedean_field[Real.real] = new
    archimedean_field[Real.real] {
    val `Fields.inverse` = (a: Real.real) => Real.inverse_reala(a)
    val `Rings.divide` = (a: Real.real, b: Real.real) => Real.divide_reala(a, b)
    val `Groups.sgn` = (a: Real.real) => Real.sgn_reala(a)
    val `Groups.abs` = (a: Real.real) => Real.abs_reala(a)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

trait floor_ceiling[A] extends archimedean_field[A] {
  val `Archimedean_Field.floor`: A => Int.int
}
def floor[A](a: A)(implicit A: floor_ceiling[A]): Int.int =
  A.`Archimedean_Field.floor`(a)
object floor_ceiling {
  implicit def `Real.floor_ceiling_real`: floor_ceiling[Real.real] = new
    floor_ceiling[Real.real] {
    val `Archimedean_Field.floor` = (a: Real.real) => Real.floor_real(a)
    val `Fields.inverse` = (a: Real.real) => Real.inverse_reala(a)
    val `Rings.divide` = (a: Real.real, b: Real.real) => Real.divide_reala(a, b)
    val `Groups.sgn` = (a: Real.real) => Real.sgn_reala(a)
    val `Groups.abs` = (a: Real.real) => Real.abs_reala(a)
    val `Groups.uminus` = (a: Real.real) => Real.uminus_reala(a)
    val `Orderings.less_eq` = (a: Real.real, b: Real.real) =>
      Real.less_eq_real(a, b)
    val `Orderings.less` = (a: Real.real, b: Real.real) => Real.less_real(a, b)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.minus` = (a: Real.real, b: Real.real) => Real.minus_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
}

def ceiling[A : floor_ceiling](x: A): Int.int =
  Int.uminus_int(floor[A](Groups.uminus[A](x)))

} /* object Archimedean_Field */

object Real {

abstract sealed class real
final case class Ratreal(a: Rat.rat) extends real

def times_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(Rat.times_rat(x, y))
}

def uminus_reala(x0: real): real = x0 match {
  case Ratreal(x) => Ratreal(Rat.uminus_rat(x))
}

def zero_reala: real = Ratreal(Rat.zero_rat)

def less_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Rat.less_rat(x, y)
}

def abs_reala(a: real): real =
  (if (less_real(a, zero_reala)) uminus_reala(a) else a)

def one_reala: real = Ratreal(Rat.one_rat)

def equal_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Rat.equal_rat(x, y)
}

def sgn_reala(a: real): real =
  (if (equal_real(a, zero_reala)) zero_reala
    else (if (less_real(zero_reala, a)) one_reala else uminus_reala(one_reala)))

def minus_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(Rat.minus_rat(x, y))
}

def plus_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(Rat.plus_rat(x, y))
}

def inverse_reala(x0: real): real = x0 match {
  case Ratreal(x) => Ratreal(Rat.inverse_rat(x))
}

def divide_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(Rat.divide_rat(x, y))
}

def less_eq_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Rat.less_eq_rat(x, y)
}

def floor_real(x0: real): Int.int = x0 match {
  case Ratreal(x) => Rat.floor_rat(x)
}

} /* object Real */

object Lista {

def nth[A](x0: List[A], x1: Nat.nat): A = (x0, x1) match {
  case (x :: xs, Nat.Suc(n)) => nth[A](xs, n)
  case (x :: xs, Nat.zero_nat()) => x
}

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => Fun.id[B]
  case (f, x :: xs) => Fun.comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def gen_length[A](n: Nat.nat, x1: List[A]): Nat.nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](Nat.Suc(n), xs)
  case (n, Nil) => n
}

def insort_key[A, B : Orderings.linorder](f: A => B, x: A, xa2: List[A]):
      List[A]
  =
  (f, x, xa2) match {
  case (f, x, Nil) => List(x)
  case (f, x, y :: ys) =>
    (if (Orderings.less_eq[B](f(x), f(y))) x :: y :: ys
      else y :: insort_key[A, B](f, x, ys))
}

def sort_key[A, B : Orderings.linorder](f: A => B, xs: List[A]): List[A] =
  (foldr[A, List[A]](((a: A) => (b: List[A]) => insort_key[A, B](f, a, b)),
                      xs)).apply(Nil)

def size_list[A]: (List[A]) => Nat.nat =
  ((a: List[A]) => gen_length[A](Nat.zero_nat(), a))

} /* object Lista */

object Percentile_Code {

def percentile_impl(values: List[Real.real], level: Real.real): Real.real =
  {
    val size: Real.real =
      Nat.of_nat[Real.real](Lista.size_list[Real.real].apply(values))
    val sorted: List[Real.real] =
      Lista.sort_key[Real.real, Real.real](((x: Real.real) => x), values)
    val i: Int.int =
      Archimedean_Field.ceiling[Real.real](Real.minus_reala(Real.times_reala(size,
                                      level),
                     Real.divide_reala(Real.Ratreal(Rat.of_int(Int.Pos(Num.Bit1(Num.Bit0(Num.One()))))),
Real.Ratreal(Rat.of_int(Int.Pos(Num.Bit0(Num.Bit1(Num.Bit0(Num.One())))))))))
    val lower: Real.real =
      Real.divide_reala(Real.minus_reala(Real.Ratreal(Rat.of_int(i)),
  Real.divide_reala(Real.Ratreal(Rat.of_int(Int.Pos(Num.Bit1(Num.Bit0(Num.One()))))),
                     Real.Ratreal(Rat.of_int(Int.Pos(Num.Bit0(Num.Bit1(Num.Bit0(Num.One())))))))),
                         size)
    val upper: Real.real =
      Real.divide_reala(Real.plus_reala(Real.Ratreal(Rat.of_int(i)),
 Real.divide_reala(Real.Ratreal(Rat.of_int(Int.Pos(Num.Bit1(Num.Bit0(Num.One()))))),
                    Real.Ratreal(Rat.of_int(Int.Pos(Num.Bit0(Num.Bit1(Num.Bit0(Num.One())))))))),
                         size)
    val lower_value: Real.real =
      Lista.nth[Real.real](sorted, Int.nat(Int.minus_int(i, Int.one_inta)))
    val upper_value: Real.real = Lista.nth[Real.real](sorted, Int.nat(i));
    Real.plus_reala(lower_value,
                     Real.divide_reala(Real.times_reala(Real.minus_reala(level,
                                  lower),
                 Real.minus_reala(upper_value, lower_value)),
Real.minus_reala(upper, lower)))
  }

} /* object Percentile_Code */
