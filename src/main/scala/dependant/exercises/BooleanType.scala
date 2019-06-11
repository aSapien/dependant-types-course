package dependant.exercises

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

  /*  TO BE SOLVED!!!

  object Step10 {
    val Bool = "Boolean" :: Type
    val b = "b" :: Bool
    val BoolInd = ("true" ::: Bool) |: ("false" ::: Bool) =: Bool
    val tru :: fls :: HNil = BoolInd.intros

    val C = "C(_ : Boolean)" :: Bool ->: Type
    val c1 = "c1" :: C(tru)
    val c2 = "c2" :: C(fls)

    val A = "A" :: Type
    val a = "a" :: A
    val Id = "_ = _" :: A ~>: (A ->: A ->: Type)
    val IdInd = ("refl" ::: A ~>>: a ~>>: (Id -> Id(A)(a)(a) )) =:: Id
    val refl :: HNil = IdInd.intros
    val B = "B" :: Type
    val f = "f" :: A ->: B
    val a1 = "a1" :: A
    val a2 = "a2" :: A
    val a3 = "a3" :: A
    //...
    map !: A ~>: a1 ~>: a2 ~>: (Id(A)(a1)(a2) ->: B ~>: f ~>: Id(B)(f(a1))(f(a2)) )
    trans !: A ~>: a1 ~>: a2 ~>: (Id(A)(a1)(a2) ->: a3 ~>: (Id(A)(a2)(a3) ->: Id(A)(a1)(a3) ))

    val ind = "ind" :: C ~>: (C(tru) ->: C(fls) ->: b ~>: C(b))
    val beta1 = "ind(c1)(c2)(true)=???" :: C ~>: c1 ~>: c2 ~>: Id(???)(???)(???)
    val beta2 = "ind(c1)(c2)(false)=???" :: C ~>: c1 ~>: c2 ~>: Id(???)(???)(???)

    val constBool = b :-> Bool

    val recBB = ind(constBool)

    val not = recBB(fls)(tru)
    val not_tru_eq_fls = beta1(constBool)(fls)(tru) !: Id(Bool)( not(tru) )(fls)
    val not_fls_eq_tru = beta2(constBool)(fls)(tru) !: Id(Bool)( not(fls) )(tru)

    val and = b :-> recBB(b)(fls)
    beta1(constBool)(tru)(fls) !: Id(Bool)( and(tru)(tru) )(tru)
    beta2(constBool)(tru)(fls) !: Id(Bool)( and(tru)(fls) )(fls)
    beta1(constBool)(fls)(fls) !: Id(Bool)( and(fls)(tru) )(fls)
    beta2(constBool)(fls)(fls) !: Id(Bool)( and(fls)(fls) )(fls)

    val not_not_b_eq_b = b :-> Id(Bool)( not(not(b)) )(b)

    val lemma1 = map(Bool)( not(tru) )(fls)( not_tru_eq_fls )(Bool)(b :-> not(b))  !: Id(Bool)( not(not(tru)) )( not(fls) )
    val lemma2 = trans(Bool)( not(not(tru)) )( not(fls) )(lemma1)(tru)( not_fls_eq_tru ) !: not_not_b_eq_b(tru)

    val lemma3 = map(Bool)( not(fls) )(tru)( not_fls_eq_tru )(Bool)(b :-> not(b))  !: Id(Bool)( not(not(fls)) )( not(tru) )
    val lemma4 = trans(Bool)( not(not(fls)) )( not(tru) )(lemma3)(fls)( not_tru_eq_fls ) !: not_not_b_eq_b(fls)

    val indNot_not_b_eq_b = ind(not_not_b_eq_b)
    indNot_not_b_eq_b(lemma2)(lemma4) !: b ~>: not_not_b_eq_b(b)
  }
  */

}
