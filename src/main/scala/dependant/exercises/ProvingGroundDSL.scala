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
}
