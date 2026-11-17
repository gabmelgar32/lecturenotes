// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//YOU DO THIS:
//Add proof blocks so the asserts hold.

//Do not change anything in the program or asserts.

val a: Z = Z.read()
val b: Z = Z.read()
var small: Z = 0

if (a < b) {
  small = a

  Deduce(
    1 ( small == a ) by Premise,
    2 ( a < b ) by Premise,
    3 ( small <= a ) by Algebra*(1),
    4 ( small < b ) by Subst_>(1, 2),
    5 ( small <= b ) by Algebra*(4)
  )
} else {
  small = b

  Deduce(
    1 ( small == b ) by Premise,
    2 (!(a < b) ) by Premise,
    3 ( small <= b ) by Algebra*(1),
    4 ( b <= a ) by Algebra*(2),
    5 ( small <= a ) by Subst_>(1, 4)
  )
}

Deduce(
    1 ( small == a | small == b ) by Premise,
    2 ( small <= a ) by Premise,
    3 ( small <= b ) by Premise
)

print("small of ", a, " and ", b, " is ", small)
assert(small <= a)
assert(small <= b)
assert(small == a | small == b)