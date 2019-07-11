abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR (c: Char) extends Rexp
case class SEQ (r1: Rexp, r2: Rexp) extends Rexp
case class ALT (r1: Rexp, r2: Rexp) extends Rexp
case class STAR (r: Rexp) extends Rexp
case class PLUS (r: Rexp) extends Rexp
case class QUE (r: Rexp) extends Rexp
case class NTIM (r: Rexp,n: Int) extends Rexp
case class UPM (r: Rexp,m: Int) extends Rexp
case class DOWNN (r: Rexp,n: Int) extends Rexp
case class NTOM (r: Rexp,n: Int,m: Int) extends Rexp

def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case PLUS(r) => nullable(r)
  case QUE(_) => true
  case NTIM(r,_) => nullable(r)
  case UPM(_,_) => true
  case DOWNN(r,_) => nullable(r)
  case NTOM(r,_,_) => nullable(r)
}


def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) =>
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case PLUS(r) => SEQ(der(c, r), STAR(r))
  case QUE(r) => der(c, r)
  case NTIM(r, n: Int) =>
    if  (n > 1 ) der(c, SEQ(r, NTIM(r, n-1)))
    else der(c, r)
  case UPM(r, m) =>
    if (m > 1) ALT(SEQ(der(c, r),UPM(r,m-1)),der(c, UPM(r, m-1)))
    else der(c, r)
  case DOWNN(r, n) => der(c, SEQ(NTIM(r, n),STAR(r)))
  case NTOM(r, n, m) => der(c, SEQ(NTIM(r, n), NTIM(QUE(r),m-n)))
}

def simp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => {
    (simp(r1), simp(r2)) match {
      case (ZERO, r2s) => r2s
      case (r1s, ZERO) => r1s
      case (r1s, r2s) =>
        if (r1s == r2s) r1s else ALT(r1s, r2s)
    }
  }
  case SEQ(r1, r2) => {
    (simp(r1), simp(r2)) match {
      case (ZERO, _) => ZERO
      case (_, ZERO) => ZERO
      case (ONE, r2s) => r2s
      case (r1s, ONE) => r1s
      case (r1s, r2s) => SEQ(r1s, r2s)
    }
  }
  case r => r
}

def ders(s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, simp(der(c, r)))
}






def matches(r: Rexp, s: String) : Boolean = nullable(ders(s.toList, r))



def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}

val reg = NTIM((CHAR('a')), 28)
var s:String = "aaaaaaaaaaaaaaaaaaaaaaaaaaaa"
println(matches(reg, s))
println(time_needed(1,matches(reg, s)))
