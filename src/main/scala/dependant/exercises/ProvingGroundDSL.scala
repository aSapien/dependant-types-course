package dependant.exercises

object ProvingGroundDSL {
  // 1.3 ProvingGround DSL

  import provingground.HoTT._
  import provingground.induction.TLImplicits._
  import shapeless._

  object Step1 {

    // For example this is declaration of type A and variable a of this type
    object Example {
      val A = "A" :: Type
      val a = "a" :: A
    }

    // Declare type Bool that should be printed as Boolean and variable b of this type
    object Exercise {
      // solution: start
      val Bool = "Boolean" :: Type
      val b = "b" :: Bool
      // solution: end
    }

  }

  object Step2 {
    val A = "A" :: Type

    // Type can depend on another type
    object Example {
      val C = "C(_ : U0)" :: Type ->: Type
      val c = "c" :: C(A)
    }

    // Declare list type List depending on type of its elements and variable l of type List(A).
    object Exercise {
      // solution: start
      val List = "List(_ : U0)" :: Type ->: Type
      val l = "l" :: List(A)
      // solution: end
    }
  }

  object Step3 {

    // Type can depend on value of another type
    object Example {
      val A = "A" :: Type
      val a = "a" :: A

      val Ba = "B(_ : A)" :: A ->: Type
      val b = "b" :: Ba(a)
    }

    // Declare vector type VecA depending on number of elements in vector (type of elements A is fixed) and variable vn of type VecA(n).
    object Exercise {
      val Nat = "Nat" :: Type
      val n = "n" :: Nat

      // solution: start
      val VecA = "VecA" :: Nat ->: Type
      val vn = "vn":: VecA(n)
      // solution: star
    }

  }

  object Step4 {
    /**
      Functions can be dependent i.e. a value can be mapped to a value of type depending on the first value.

      Arrows :-> and :~> are for lambdas (ordinary and dependent correspondingly).

      Arrows ->: and ~>: are for function types (ordinary and dependent correspondingly).

      For example this is identity function:

      val id = A :~> (a :-> a)  !: A ~>: (A ->: A)
     */
    object Example {
      val A = "A" :: Type
      val B = "B" :: Type
      val F = "F(_ : U0)" :: Type ->: Type
      val a = "a" :: A
      val b = "b" :: B
      val fa = "fa" :: F(A)
      val fb = "fb" :: F(B)
      val opABA = "op" :: A ->: B ->: A
      val opABB = "op" :: A ->: B ->: B
      val foldlF = "foldl(F)" :: (A ->: B ->: A) ->: A ->: F(B) ->: A
      val foldrF = "foldr(F)" :: (A ->: B ->: B) ->: B ->: F(A) ->: B

      F :~> (fb :-> (opABA :-> (a :-> foldlF(opABA)(a)(fb) ))) !: F ~>: (F(B) ->: (A ->: B ->: A) ->: A ->: A)
      F :~> (fa :-> (b :-> (opABB :-> foldrF(opABB)(b)(fa) ))) !: F ~>: (F(A) ->: B ->: (A ->: B ->: B) ->: B)
      b :-> (opABB :-> (F :~> (fa :-> foldrF(opABB)(b)(fa) ))) !: B ->: (A ->: B ->: B) ->: F ~>: (F(A) ->: B)
    }

    // Write type of lambda F :~> (A :~> (fa :-> (B :~> (f :-> mapF(A)(B)(f)(fa) )))).
    object Exercise {
      val A = "A" :: Type
      val B = "B" :: Type
      val F = "F(_ : U0)" :: Type ->: Type
      val fa = "fa" :: F(A)

      val mapF = "map(F)" :: A ~>: B ~>: ((A ->: B) ->: F(A) ->: F(B) )
      val f = "f" :: A ->: B

      // solution: start
      val T = F ~>: (A ~>: (F(A) ->: (B ~>: ((A ->: B) ->: F(B)))))
      // solution: end

      F :~> (A :~> (fa :-> (B :~> (f :-> mapF(A)(B)(f)(fa) )))) !: T

    }
  }

  object Step5 {
    // Write a lambda of type A ~>: F ~>: (F(A) ->: (A ->: Bool) ->: F(A) ).
    object Exercise {
      val A = "A" :: Type
      val F = "F(_ : U0)" :: Type ->: Type
      val fa = "fa" :: F(A)

      val Bool = "Boolean" :: Type
      val filterF = "filter(F)" :: A ~>: ((A ->: Bool) ->: F(A) ->: F(A))
      val p = "p" :: A ->: Bool

      // solution: start
      val g = A :~> (F :~> (fa :-> (p :-> filterF(A)(p)(fa))))
      // solution: end

      g !: A ~>: F ~>: (F(A) ->: (A ->: Bool) ->: F(A) )
    }
  }

  object Step6 {
    object Example {
      // Boolean type
      // Declaration
      val Bool = "Boolean" :: Type
      // Types of constructors in the form ("how to print constructor" ::: Type_of_constructor)
      val BoolInd = ("true" ::: Bool) |: ("false" ::: Bool) =: Bool
      // HList of all constructors for this inductive type
      val tru :: fls :: HNil = BoolInd.intros

      /**
        * More examples:
        *
        * -- Type of natural numbers
        * val Nat = "Nat" :: Type
        * val NatInd = ("0" ::: Nat) |: ("succ" ::: Nat -->>: Nat) =: Nat
        * val zero :: succ :: HNil = NatInd.intros
        *
        * -- Type of integers
        * val Int = "Integer" :: Type
        * val IntInd = ("pos" ::: Nat ->>: Int) |: ("neg" ::: Nat ->>: Int) =: Int
        * val pos :: neg :: HNil = IntInd.intros
        *
        * -- List type (type of elements A is fixed)
        * val ListA = "List(A)" :: Type
        * val ListAInd = ("nil" ::: ListA) |: ("cons" ::: A ->>: ListA -->>: ListA) =: ListA
        * val nil :: cons :: HNil = ListAInd.intros
        *
        * -- Type of binary trees (option 1)
        * val BTree = "BTree" :: Type
        * val BTreeInd = ("leaf" ::: BTree) |: ("fork" ::: BTree -->>: BTree -->>: BTree) =: BTree
        * val leaf :: fork :: HNil = BTreeInd.intros
        *
        * -- Type of binary trees (option 2)
        * val BTree = "BTree" :: Type
        * val BTreeInd = ("leaf" ::: BTree) |: ("fork" ::: (Bool -|>: BTree) -->>: BTree) =: BTree
        * val leaf :: fork :: HNil = BTreeInd.intros
        */

    }

    // Translate the following algebraic data type from plain Scala into ProvingGround DSL
    object Exercise {
      sealed trait Expression
      case class Number(n: Int) extends Expression
      case class Negate(e: Expression) extends Expression
      case class Add(e1: Expression, e2: Expression) extends Expression
      case class Mult(e1: Expression, e2: Expression) extends Expression

      // provided in scope: start
      val Nat = "Nat" :: Type
      val NatInd = ("0" ::: Nat) |: ("succ" ::: Nat -->>: Nat) =: Nat
      val zero :: succ :: HNil = NatInd.intros

      val Int = "Integer" :: Type
      val IntInd = ("pos" ::: Nat ->>: Int) |: ("neg" ::: Nat ->>: Int) =: Int
      val pos :: neg :: HNil = IntInd.intros

      val Expr = "Expression" :: Type
      // provided in scope: end

      // solution: start
      val ExprInd =
        ("Number" ::: Int ->>: Expr) |:
        ("Negate" ::: Expr -->>: Expr) |:
        ("Add" ::: (Expr -->>: Expr -->>: Expr)) |:
        ("Mult" ::: (Expr -->>: Expr -->>: Expr)) =: Expr
      // solution: end

      val number :: negate :: add :: mult :: HNil = ExprInd.intros
    }
  }

  object Step7 {
    /**
      * If we define dependent inductive type then we should use =:: instead of =:
      * and (Type_name -> Type_name(n)) in output type, (Type_name :> Type_name(n)) in input type
      * instead of just Type_name(n).
      *
      * In dependent function types we should use arrow ~>>: instead of ->>:
      */
    object Example {
      /**
        * -- For example this is vector type (type of elements A is fixed)
        * val VecA = "Vec(A)" :: Nat ->: Type
        * val n = "n" :: Nat
        * val VecAInd = ("nil" ::: (VecA -> VecA(zero) )) |:
        * {"cons" ::: n ~>>: (A ->>: (VecA :> VecA(n) ) -->>: (VecA -> VecA(succ(n)) ))} =:: VecA
        * val vnil :: vcons :: HNil = VecAInd.intros
        *
        * -- Type of natural numbers less than n
        * val Fin = "Fin" :: Nat ->: Type
        * val FinInd = {"FZ" ::: n ~>>: (Fin -> Fin(succ(n)) )} |:
        * {"FS" ::: n ~>>: ((Fin :> Fin(n) ) -->>: (Fin -> Fin(succ(n)) ))} =:: Fin
        * val fz :: fs :: HNil = FinInd.intros
        *
        * -- Vector type (type of elements A is arbitrary)
        * val Vec = "Vec" :: Type ->: Nat ->: Type
        * val VecInd = {"nil" ::: A ~>>: (Vec -> Vec(A)(zero) )} |:
        * {"cons" ::: A ~>>: n ~>>: (A ->>: (Vec :> Vec(A)(n) ) -->>: (Vec -> Vec(A)(succ(n)) ))} =:: Vec
        * val vnil :: vcons :: HNil = VecInd.intros
        *
        * -- Type of type-level lists and heterogeneous lists
        * val TLst = "TList" :: Type
        * val TLstInd = ("nil" ::: TLst) |: ("cons" ::: Type ->>: TLst -->>: TLst) =: TLst
        * val tnil :: tcons :: HNil = TLstInd.intros
        * val tlst = "tlist" :: TLst
        *
        * val HLst = "HList" :: TLst ->: Type
        * val HLstInd = {"nil" ::: HLst -> HLst(tnil) } |:
        * {"cons" ::: A ~>>: (A ->>: (tlst ~>>: ((HLst :> HLst(tlst) ) -->>: (HLst -> HLst(tcons(A)(tlst)) ))))} =:: HLst
        * val hnil :: hcons :: HNil = HLstInd.intros
        *
        * -- Identity type
        * val Id = "=" :: A ~>: (A ->: A ->: Type)
        * val IdInd = ("refl" ::: A ~>>: a ~>>: (Id -> Id(A)(a)(a) )) =:: Id
        * val refl :: HNil = IdInd.intros
        *
        * -- Heterogeneous identity type
        * val HId = "HId" :: A ~>: B ~>: (A ->: B ->: Type)
        * val HIdInd = ("refl" ::: A ~>>: a ~>>: (HId -> HId(A)(A)(a)(a) )) =:: HId
        * val hrefl :: HNil = HIdInd.intros
        *
        * -- Type "less than or equal"
        * val LTE = "≤" :: Nat ->: Nat ->: Type
        * val LTEInd = {"0 ≤ _" ::: m ~>>: (LTE -> LTE(zero)(m) )} |:
        * {"S _ ≤ S _" ::: n ~>>: m ~>>: ((LTE :> LTE(n)(m) ) -->>: (LTE -> LTE(succ(n))(succ(m)) ))} =:: LTE
        * val lteZero :: lteSucc :: HNil = LTEInd.intros
        *
        * -- Parity type
        * val Parity = "Parity" :: Nat ->: Type
        * val ParityInd = {"even" ::: n ~>>: (Parity -> Parity(double(n)) )} |:
        * {"odd" ::: n ~>>: (Parity -> Parity(succ(double(n))) )} =:: Parity
        * val even :: odd :: HNil = ParityInd.intros
        *
        */

    }

    // Translate the following algebraic data type from plain Scala into ProvingGround DSL (type of elements A is arbitrary)
    object Exercise {
      sealed trait List[A]
      case class Nil[A]() extends List[A]
      case class Cons[A](a: A, as: List[A]) extends List[A]


      val List = "List" :: Type ->: Type

      // provided in scope: start
      val A = "A" :: Type
      // provided in scope: end

      // solution: start
      val ListInd =
        ("nil" ::: A ~>>: (List -> List(A) )) |:
        ("cons" ::: A ~>>: (A ->>: (List :> List(A)) -->>: (List -> List(A)))) =:: List
      // solution: end

      val nil :: cons :: HNil = ListInd.intros
    }
  }
}
