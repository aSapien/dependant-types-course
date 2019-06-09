import provingground.HoTT._
import provingground.induction.ConstructorSeqTL
import provingground.induction.TLImplicits._
import provingground.translation.FansiShow._
import shapeless._

object Main {

  val A: Typ[Term] = "A" :: Type
  val a: Term = "a" :: A

  val Bool: Typ[Term] = "Boolean" :: Type
  val BoolInd: ConstructorSeqTL[HNil :: HNil :: HNil, Term, Term :: Term :: HNil] = ("true" ::: Bool) |: ("false" ::: Bool) =: Bool
  val tru :: fls :: HNil = BoolInd.intros
  val recBB: Func[Term, Func[Term, Func[Term, Term]]] = BoolInd.rec(Bool)
  val not: Func[Term, Term] = recBB(fls)(tru)

  def main(args: Array[String]): Unit = {
    println(A) // A
    println(a) // a
    println(a !: A) // a
    println(a.typ) // A
    println(Bool) // Boolean
    println(BoolInd) // ConstructorSeqTL(Cons(true,IdShape(),Cons(false,IdShape(),Empty())),Boolean)
    println(tru) // true
    println(fls) // false
    println(recBB) // (RecDataSym(true) :  Boolean) ↦ ((RecDataSym(false) :  Boolean) ↦ (rec(Boolean)(Boolean)(RecDataSym(true))(RecDataSym(false))))
    println(recBB.fansi) // (RecDataSym(true) : Boolean) ↦ (RecDataSym(false) : Boolean) ↦ rec_{ Boolean ; Boolean }(RecDataSym(true))(RecDataSym(false))
    println(not) // rec(Boolean)(Boolean)(false)(true)
    println(not.fansi) // rec_{ Boolean ; Boolean }(false)(true)
  }

}
