import scala.util.Try

abstract class State



case class TState(i: Int) extends State

type :=>[A, B] = PartialFunction[A, B]
type NFAtrans = (TState, Char) :=> Set[TState]
type eNFAtrans = (TState, Option[Char]) :=> Set[TState]

def applyOrElse[A, B](f: A :=> Set[B], x: A) : Set[B] =
  Try(f(x)) getOrElse Set[B]()

// for composing an eNFA transition with a NFA transition
implicit class RichPF(val f: eNFAtrans) extends AnyVal {
  def +++(g: NFAtrans) : eNFAtrans =
  { case (q, None) => applyOrElse(f, (q, None))
  case (q, Some(c)) =>
    applyOrElse(f, (q, Some(c))) | applyOrElse(g, (q, c)) }
}

case class NFA[A, C](starts: Set[A], // starting states
                     delta: (A, C) :=> Set[A], // transition function
                     fins: A => Boolean) { // final states

  // given a state and a character, what is the set of
  // next states? if there is none => empty set
  def next(q: A, c: C) : Set[A] =
    applyOrElse(delta, (q, c))

  def nexts(qs: Set[A], c: C) : Set[A] =
    qs.flatMap(next(_, c))

  // given some states and a string, what is the set
  // of next states?
  def deltas(q: A, s: List[C]) : Boolean = s match {                      //here is deep-first search
    case Nil => fins(q)
    case c::cs => next(q, c).exists(deltas(_, cs))
  }
  def accepts(s: List[C]) : Boolean =
    starts.exists(deltas(_, s))

}

import scala.annotation.tailrec
@tailrec
def fixpT[A](f: A => A, x: A): A = {
  val fx = f(x)
  if (fx == x) x else fixpT(f, fx)
}

// translates eNFAs directly into NFAs
def eNFA[A, C](starts: Set[A], // starting states
               delta: (A, Option[C]) :=> Set[A], // epsilon-transitions
               fins: A => Boolean) : NFA[A, C] = { // final states

  // epsilon transitions
  def enext(q: A) : Set[A] =
    applyOrElse(delta, (q, None))

  def enexts(qs: Set[A]) : Set[A] =
    qs | qs.flatMap(enext(_)) // | is the set-union in Scala

  // epsilon closure
  def ecl(qs: Set[A]) : Set[A] =
    fixpT(enexts, qs)

  // "normal" transitions
  def next(q: A, c: C) : Set[A] =
    applyOrElse(delta, (q, Some(c)))

  def nexts(qs: Set[A], c: C) : Set[A] =
    ecl(ecl(qs).flatMap(next(_, c)))

  // result NFA
  NFA(ecl(starts),
    { case (q, c) => nexts(Set(q), c) },
    q => ecl(Set(q)) exists fins)
}




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


object TState {
  var counter = 0

  def apply() : TState = {
    counter += 1
    new TState(counter - 1)
  }
}


case class DFA[A, C](start: A, // starting state
                     delta: (A, C) :=> A, // transition (partial fun)
                     fins: A => Boolean) { // final states

  def deltas(q: A, s: List[C]): A = s match {
    case Nil => q
    case c :: cs => deltas(delta(q, c), cs)
  }

  def accepts(s: List[C]): Boolean =
    Try(fins(deltas(start, s))) getOrElse false
}




// a type abbreviation
type NFAt = NFA[TState, Char]


// a NFA that does not accept any string
def NFA_ZERO(): NFAt = {
  val Q = TState()
  NFA(Set(Q), { case _ => Set() }, Set())
}

// a NFA that accepts the empty string
def NFA_ONE() : NFAt = {
  val Q = TState()
  NFA(Set(Q), { case _ => Set() }, Set(Q))
}

// a NFA that accepts the string "c"
def NFA_CHAR(c: Char) : NFAt = {
  val Q1 = TState()
  val Q2 = TState()
  NFA(Set(Q1), { case (Q1, d) if (c == d) => Set(Q2) }, Set(Q2))
}

// sequence of two NFAs
def NFA_SEQ(enfa1: NFAt, enfa2: NFAt) : NFAt = {
  val new_delta : eNFAtrans =
  { case (q, None) if enfa1.fins(q) => enfa2.starts }

  eNFA(enfa1.starts, new_delta +++ enfa1.delta +++ enfa2.delta,
    enfa2.fins)
}

// alternative of two NFAs
def NFA_ALT(enfa1: NFAt, enfa2: NFAt) : NFAt = {
  val new_delta : NFAtrans = {
    case (q, c) => applyOrElse(enfa1.delta, (q, c)) |
      applyOrElse(enfa2.delta, (q, c)) }
  val new_fins = (q: TState) => enfa1.fins(q) || enfa2.fins(q)

  NFA(enfa1.starts | enfa2.starts, new_delta, new_fins)
}

// star of a NFA
def NFA_STAR(enfa: NFAt) : NFAt = {
  val Q = TState()
  val new_delta : eNFAtrans =
  { case (Q, None) => enfa.starts
  case (q, None) if enfa.fins(q) => Set(Q) }

  eNFA(Set(Q), new_delta +++ enfa.delta, Set(Q))
}



def thompson(r: Rexp) : NFAt = r match {
  case ZERO => NFA_ZERO()
  case ONE => NFA_ONE()
  case CHAR(c) => NFA_CHAR(c)
  case ALT(r1, r2) => NFA_ALT(thompson(r1), thompson(r2))
  case SEQ(r1, r2) => NFA_SEQ(thompson(r1), thompson(r2))
  case STAR(r1) => NFA_STAR(thompson(r1))
}


def subset[A, C](nfa: NFA[A, C]) : DFA[Set[A], C] = {
  DFA(nfa.starts,
    { case (qs, c) => nfa.nexts(qs, c) },
    _.exists(nfa.fins))
}

def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}



val reg = SEQ(STAR(CHAR('a')),CHAR('b'))
print(subset(thompson(reg)).accepts("aaaaaaaab".toList))
print(time_needed(1,subset(thompson(STAR(CHAR('a')))).accepts("aaaaaaaa".toList)))
