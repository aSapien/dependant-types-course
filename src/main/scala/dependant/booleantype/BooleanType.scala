package dependant.booleantype

object BooleanType {
  // 1.2 Boolean type

  import provingground.HoTT._
  import provingground.induction.TLImplicits._
  import shapeless._

  object Step3 {
    val Bool = "Boolean" :: Type
    val b = "b" :: Bool
    val BoolInd = ("true" ::: Bool) |: ("false" ::: Bool) =: Bool
    val tru :: fls :: HNil = BoolInd.intros
    val recBB = BoolInd.rec(Bool)


    // solution: start
    val or = b :-> recBB(tru)(b)
    // solution: end

    assert(or(tru)(fls) == tru)
    assert(or(tru)(tru) == tru)
    assert(or(fls)(tru) == tru)
    assert(or(fls)(fls) == fls)
  }


  object Step4 {
    val Bool = "Boolean" :: Type
    val b = "b" :: Bool
    val BoolInd = ("true" ::: Bool) |: ("false" ::: Bool) =: Bool
    val tru :: fls :: HNil = BoolInd.intros
    val recBB = BoolInd.rec(Bool)
    val not = recBB(fls)(tru)

    // solution: start
    val xor = b :-> recBB(not(b))(b)
    // solution: end

    assert(xor(tru)(tru) == fls)
    assert(xor(fls)(fls) == fls)
    assert(xor(tru)(fls) == tru)
    assert(xor(fls)(tru) == tru)
  }

  object Step5 {
    val Bool = "Boolean" :: Type
    val b = "b" :: Bool
    val BoolInd = ("true" ::: Bool) |: ("false" ::: Bool) =: Bool
    val tru :: fls :: HNil = BoolInd.intros
    val recBB = BoolInd.rec(Bool)
    val not = recBB(fls)(tru)

    // solution: start
    val isEqual = b :-> recBB(b)(not(b))
    // solution: end

    assert(isEqual(fls)(fls) == tru)
    assert(isEqual(fls)(tru) == fls)
    assert(isEqual(tru)(fls) == fls)
    assert(isEqual(tru)(tru) == tru)
  }

  object Step6 {
    val Bool = "Boolean" :: Type
    val b = "b" :: Bool
    val BoolInd = ("true" ::: Bool) |: ("false" ::: Bool) =: Bool
    val tru :: fls :: HNil = BoolInd.intros
    val recBBB = BoolInd.rec(Bool ->: Bool)

    // solution: start
    val or = recBBB(b :-> tru)(b :-> b)
    // solution: end

    assert(or(tru)(fls) == tru)
    assert(or(tru)(tru) == tru)
    assert(or(fls)(fls) == fls)
    assert(or(fls)(tru) == tru)
  }

  object Step7 {
    val Bool = "Boolean" :: Type
    val b = "b" :: Bool
    val BoolInd = ("true" ::: Bool) |: ("false" ::: Bool) =: Bool
    val tru :: fls :: HNil = BoolInd.intros
    val recBB = BoolInd.rec(Bool)
    val not = recBB(fls)(tru)
    val recBBB = BoolInd.rec(Bool ->: Bool)

    // solution: start
    val xor = recBBB(b :-> not(b))(b :-> b)
    // solution: end

    assert(xor(tru)(tru) == fls)
    assert(xor(fls)(fls) == fls)
    assert(xor(tru)(fls) == tru)
    assert(xor(fls)(tru) == tru)
  }

  object Step8 {
    val Bool = "Boolean" :: Type
    val b = "b" :: Bool
    val BoolInd = ("true" ::: Bool) |: ("false" ::: Bool) =: Bool
    val tru :: fls :: HNil = BoolInd.intros
    val recBB = BoolInd.rec(Bool)
    val not = recBB(fls)(tru)
    val recBBB = BoolInd.rec(Bool ->: Bool)

    // solution: start
    val isEqual = recBBB(b :-> b)(b :-> not(b))
    // solution: end

    assert(isEqual(fls)(fls) == tru)
    assert(isEqual(fls)(tru) == fls)
    assert(isEqual(tru)(fls) == fls)
    assert(isEqual(tru)(tru) == tru)
  }

  object Step9 {
    val Bool = "Boolean" :: Type
    val b = "b" :: Bool
    val BoolInd = ("true" ::: Bool) |: ("false" ::: Bool) =: Bool
    val tru :: fls :: HNil = BoolInd.intros

    val C = "C" :: Type
    val c1 = "c1" :: C
    val c2 = "c2" :: C

    val A = "A" :: Type
    val a = "a" :: A
    val Id = "Id" :: A ~>: (A ->: A ->: Type)
    val IdInd = ("refl" ::: A ~>>: a ~>>: (Id -> Id(A)(a)(a) )) =:: Id
    val refl :: HNil = IdInd.intros

    val rec = "rec" :: C ~>: (C ->: C ->: Bool ->: C)

    // solution: start
    val beta1 = "rec(c1)(c2)(true)=???" :: C ~>: c1 ~>: c2 ~>: Id(C)( rec(C)(c1)(c2)(tru) )(c1)
    val beta2 = "rec(c1)(c2)(false)=???" :: C ~>: c1 ~>: c2 ~>: Id(C)( rec(C)(c1)(c2)(fls) )(c2)
    // solution: end

    val recBB = rec(Bool)

    val not = recBB(fls)(tru)
    beta1(Bool)(fls)(tru) !: Id(Bool)( not(tru) )(fls)
    beta2(Bool)(fls)(tru) !: Id(Bool)( not(fls) )(tru)

    val and = b :-> recBB(b)(fls)
    beta1(Bool)(tru)(fls) !: Id(Bool)( and(tru)(tru) )(tru)
    beta2(Bool)(tru)(fls) !: Id(Bool)( and(tru)(fls) )(fls)
    beta1(Bool)(fls)(fls) !: Id(Bool)( and(fls)(tru) )(fls)
    beta2(Bool)(fls)(fls) !: Id(Bool)( and(fls)(fls) )(fls)
  }
}
