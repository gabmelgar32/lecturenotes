// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//finding x*y by doing x + x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //What can we use as the function contract?
  Contract(
    Requires(y >= 0), //because our condition is y ==0, we want our else to be greater than 0 otherwise it will get infinitely smaller
    Ensures(Res[Z] == x * y)
  )


  var total: Z = 0
  var i: Z = 0

  //what goes here?
  //- need to prove the invariant is true initially
  Deduce(
    1(total == 0) by Premise,
    2(i == 0) by Premise,
    3(total == i*x) by Algebra*(1,2)
    //need: total == i * x (the variant)
  )

  while (i != y) {
    //what goes here?
    Invariant(
      //first list the variables that are changing
      Modifies(total, i),
      //now list the invariants
      total == i * x
    )

    //could list the invariant as a premise
    //total == i *x by Premise
    total = total + x
    Deduce(
      1(Old(total) == i *x) by Premise, //from invariant
      2(total == Old(total) + x) by Premise, //from assignment
      3(total == i * x + x) by Algebra*(1,2)// process without old
    )
    i = i + 1

    //what should we be able to assert here?
    //-want to prove the invaraiant is still true
    //need:total == i * x
    Deduce(
      1(i == Old(i) + 1) by Premise, //from assignemnt
      2(total == Old(i)*x + x) by Premise, //from previous block
      3(Old(i) == i - 1) by Algebra*(1),
      4(total == (i-1)*x + x) by Algebra*(2,3),
      5(total == i*x - x + x) by Algebra*(4),
      6(total == i * x) by Algebra*(5),
    )
  }

  //what do we need here?
  Deduce(
    1( !(i != y) ) by Premise,
    2(i == y) by Algebra*(1),
    3(total == i*x) by Premise,// loop invafriant is true
    4(total == x*y) by Algebra*(2,3) // 
  )

  return total
}

//////////// test code /////////

val a: Z = 5
val b: Z = 4

var ans: Z = mult(a, b)

//what do we want to assert that ans is?