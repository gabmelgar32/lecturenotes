// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def absVal(numOrig: Z) : Z = {
  //what do we need here?
  Contract(
    //no preconditions
    Ensures( Res[Z] >= 0, Res[Z] == numOrig * -1 | Res[Z] == numOrig )
  )

  var num: Z = numOrig

  //update num to be the absolute value of the input
  if (num < 0) {
    num = num * -1

    Deduce(
    1 ( Old(num) == numOrig  ) by Premise, //from assignment statement, but num has changed
    2 ( Old(num) < 0 ) by Premise, //condition true, but num has changed
    3 ( num == Old(num) * -1 ) by Premise, //from assignment statement, but num has changed

    //need: num == numOrig*-1 
    4 ( num == numOrig * -1 ) by Algebra*(1, 3),
    5 ( num >= 0 ) by Algebra*(2,3)
  )
  } else {
    //do nothing -- num is already its own absolute value
    Deduce(
      1 ( !(num < 0) ) by Premise, //condition is false
      2 ( num >= 0 ) by Algebra*(1), //needed for assert
      3 ( num == numOrig ) by Premise //from assignment
    )
  }

  //what can we say here?
  //what do we need to prove by the end of the function?
  Deduce(
    //proves postcondition
    1 ( num >= 0 ) by Premise, //true in both branches
    2 ( num == numOrig * -1 | num == numOrig ) by Premise //LHS from if, RHS from else
    //need: num >= 0
    //need: num == numOrig*-1 in if
    //need: num == numOrig in else
  )

  return num

}

////////////////// Test code //////////////

val x: Z = -4

//no preconditions to prove

//use function to get absolute value of x
//what *should* the absolute value be?
val answer: Z = absVal(x)

Deduce(
  1 ( x == -4 ) by Premise, //from assignment
  2 ( answer >= 0 ) by Premise, //from postcondition
  3 ( answer == x * -1 | answer == x ) by Premise,

  //use OrE to get assert
  4 SubProof(
    5 Assume( answer == x * -1 ),
    6 ( answer == 4 ) by Algebra*(1,5)

    //goal: answer == 4
  ),
  7 SubProof(
    8 Assume (answer == x ),
    9 ( F ) by Algebra*(8,1,2),
    10 ( answer == 4 ) by BottomE(9)

    //goal: answer == 4
  ),
  11 ( answer == 4 ) by OrE(3, 4, 7)


  //answer == 4
)


//what should we be able to assert?
assert(answer == 4)