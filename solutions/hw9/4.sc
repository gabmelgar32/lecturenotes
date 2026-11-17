// #Sireum #Logika
//@Logika: --manual
import org.sireum._
import org.sireum.justification._

//YOU DO THIS:
//Add deduce blocks so each assert holds

//Do not change anything in the program or asserts.

//this block is needed in order to divide by 3
Deduce(
    1 ( 3 != 0 ) by Algebra T
)

var x: Z = Z.prompt("Enter a number: ")
val xOrig: Z = x

x = x * 2
Deduce(
    1 ( x == Old(x)*2 ) by Premise,
    2 ( xOrig == Old(x) ) by Premise,
    3 ( x == xOrig*2 )  by Algebra*(2, 1)
)

assert(x == xOrig*2)

x = x + xOrig
Deduce(
    1 ( x == Old(x) + xOrig  ) by Premise,
    2 ( Old(x) == xOrig*2 )  by Premise,
    3 ( x == xOrig*3) by Algebra*(1,2)
)

assert(x == xOrig*3)

x = x / 3
Deduce(
    1 ( x == Old(x) / 3  ) by Premise,
    2 ( Old(x) == xOrig*3) by Premise,
    3 ( x == (xOrig*3) / 3 ) by Subst_<(2, 1),
    4 ( x == xOrig ) by Algebra*(3)
)

assert(x == xOrig )

x = x - xOrig
Deduce(
    1 ( x == Old(x) - xOrig ) by Premise,
    2 ( Old(x) == xOrig  ) by Premise,
    3 ( x == xOrig - xOrig ) by Subst_<(2, 1),
    4 ( x == 0  ) by Algebra*(3)
)

print("No matter what you entered, you are back to 0")
assert(x == 0)