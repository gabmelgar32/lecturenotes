// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var num: Z = Z.prompt("Enter a number: ")
val numOrig : Z = num


//abs of 4 is 4
//abs of -4 is 4

if (num < 0) {
  num = num * -1

  Deduce(
    1 ( numOrig == Old(num) ) by Premise, //from assignment statement, but num has changed
    2 ( Old(num) < 0 ) by Premise, //condition true, but num has changed
    3 ( num == Old(num) * -1 ) by Premise, //from assignment statement, but num has changed

    //need: num == numOrig*-1 
    4 ( num == numOrig * -1 ) by Algebra*(1, 3),
    5 ( num >= 0 ) by Algebra*(2,3)
  )

} else {
  //no code, just for verification

  Deduce(
    1 ( !(num < 0) ) by Premise, //condition is false
    2 ( numOrig == num ) by Premise, //from assignment
    3 ( num >= 0 ) by Algebra*(1), //needed for assert
    4 ( num == numOrig ) by Algebra*(2) //needed for assert
  )
}

//need to prove:
//num>=0 in both branches
//num == numOrig*-1 in if
//num == numOrig in else

Deduce(
  1 ( num >= 0 ) by Premise, //true in both branches
  2 ( num == numOrig * -1 | num == numOrig ) by Premise //LHS from if, RHS from else
  //need: num >= 0
  //need: num == numOrig*-1 in if
  //need: num == numOrig in else
)


//How can we assert that num is the absolute value of the input?
//(what was the original input?)

assert(num >= 0)
assert(num == numOrig * -1 | num == numOrig)