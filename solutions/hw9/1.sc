// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

val x: Z = Z.prompt("Enter a positive integer: ")
assume(x > 0)

val y: Z = Z.prompt("Enter a positive integer: ")
assume(y > 0)

val answer: Z = x + y

//YOU DO THIS:
//Write a deduce block so that the assert at the end holds.
//Do not change anything in the program or assert.

Deduce(
    1 ( x > 0 ) by Premise,
    2 ( y > 0 ) by Premise,
    3 ( answer == x + y ) by Premise,
    4 ( answer >= x ) by Algebra*(1,2,3),
    5 ( answer >= y  ) by Algebra*(1,2,3),
    6 ( answer >= x & answer >= y ) by AndI(4, 5),
    7 ( answer >= 2 ) by Algebra*(1,2,3),
    8 ( answer >= x & answer >= y & answer >= 2 ) by AndI(6, 7)
)

assert(answer >= x & answer >= y & answer >= 2)