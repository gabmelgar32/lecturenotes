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
} else {
  //no code, just for verification

}

//need to prove:
//num>=0 in both branches
//num == numOrig*-1 in if
//num == numOrig in else


//How can we assert that num is the absolute value of the input?
//(what was the original input?)

assert(num >= 0)
assert(num == numOrig*-1 | num == numOrig)